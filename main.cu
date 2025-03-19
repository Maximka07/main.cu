#include <iostream>
#include <string>
#include <cuda_runtime.h>
#include <vector>
#include <fstream>
#include <random>
#include <future>
#include <sqlite3.h>
#include "third-party/secp256k1/inc_ecc_secp256k1.h"
#include "third-party/keccak/keccak256.h"
#include "bip39_wordlist.h"

typedef unsigned char u8;

std::string generate_mnemonic() {
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_int_distribution<> dis(0, bip39_wordlist.size() - 1);
    std::string mnemonic;
    for (int i = 0; i < 12; i++) {
        mnemonic += bip39_wordlist[dis(gen)];
        if (i < 11) mnemonic += " ";
    }
    return mnemonic;
}

void mnemonic_to_seed(const std::string& mnemonic, uint8_t* seed) {
    std::string salt = "mnemonic";
    std::string input = mnemonic + salt;
    for (int i = 0; i < 64; i++) {
        seed[i] = input[i % input.length()];
    }
}

#define CUDA_CHECK(call) \
    do { \
        cudaError_t err = call; \
        if (err != cudaSuccess) { \
            std::cerr << "CUDA Error: " << cudaGetErrorString(err) << " at " << __FILE__ << ":" << __LINE__ << std::endl; \
            exit(1); \
        } \
    } while(0)

struct WalletInfo {
    uint8_t private_key[32];
    uint8_t address[20];
    bool found;
};

// Вспомогательные функции для Keccak-256
__device__ u64 rotl64(u64 x, int i) {
    return ((0U + x) << i) | (x >> ((64 - i) & 63));
}

__device__ void keccak256_absorb(u64* state, const int* rotation) {
    u8 r = 1;  // LFSR
    for (int i = 0; i < 24; i++) {
        u64 c[5] = {};
        for (int x = 0; x < 5; x++) {
            for (int y = 0; y < 5; y++)
                c[x] ^= state[x + y + (y << 2)];
        }
        for (int x = 0; x < 5; x++) {
            u64 d = c[(x + 4) % 5] ^ rotl64(c[(x + 1) % 5], 1);
            for (int y = 0; y < 5; y++)
                state[x + y + (y << 2)] ^= d;
        }
        u64 b[5][5];
        for (int x = 0; x < 5; x++) {
            for (int y = 0; y < 5; y++)
                b[y][(x * 2 + y * 3) % 5] = rotl64(state[x + y + (y << 2)], rotation[(x << 2) + x + y]);
        }
        for (int x = 0; x < 5; x++) {
            for (int y = 0; y < 5; y++)
                state[x + y + (y << 2)] = b[x][y] ^ (~b[(x + 1) % 5][y] & b[(x + 2) % 5][y]);
        }
        for (int j = 0; j < 7; j++) {
            state[0] ^= (u64)(r & 1) << ((1 << j) - 1);
            r = (u8)((r << 1) ^ ((r >> 7) * 0x171));
        }
    }
}

__device__ void keccak256_update_state(u64* state, const u8* msg, const u32 len) {
    const int rotation[25] = {
        0, 36,  3, 41, 18,
        1, 44, 10, 45,  2,
        62,  6, 43, 15, 61,
        28, 55, 25, 21, 56,
        27, 20, 39,  8, 14
    };
    u32 blockOff = 0;
    for (u32 i = 0; i < len; i++) {
        u32 j = blockOff >> 3;
        u32 xj = j % 5;
        u32 yj = j / 5;
        state[xj + yj + (yj << 2)] ^= (u64)(msg[i]) << ((blockOff & 7) << 3);
        blockOff++;
        if (blockOff == KECCAK256_BLOCKSIZE) {
            keccak256_absorb(state, rotation);
            blockOff = 0;
        }
    }
    int i = blockOff >> 3;
    u32 xi = i % 5;
    u32 yi = i / 5;
    state[xi + yi + (yi << 2)] ^= UINT64_C(0x01) << ((blockOff & 7) << 3);
    blockOff = KECCAK256_BLOCKSIZE - 1;
    int j = blockOff >> 3;
    u32 xj = j % 5;
    u32 yj = j / 5;
    state[xj + yj + (yj << 2)] ^= UINT64_C(0x80) << ((blockOff & 7) << 3);
    keccak256_absorb(state, rotation);
}

__device__ void keccak256_get_hash(u8* r, const u8* msg, const u32 len) {
    u64 state[25] = {};
    keccak256_update_state(state, msg, len);
    for (int i = 0; i < KECCAK256_HASH_LEN; i++) {
        int j = i >> 3;
        u32 xj = j % 5;
        u32 yj = j / 5;
        r[i] = (u8)(state[xj + yj + (yj << 2)] >> ((i & 7) << 3));
    }
}

// Вспомогательные функции для secp256k1
__device__ u32 sub(u32 *r, const u32 *a, const u32 *b) {
    u32 c = 0;
    for (int i = 0; i < 8; i++) {
        u64 t = (u64)a[i] - b[i] - c;
        r[i] = (u32)t;
        c = (t >> 32) & 1;
    }
    return c;
}

__device__ u32 add(u32 *r, const u32 *a, const u32 *b) {
    u32 c = 0;
    for (int i = 0; i < 8; i++) {
        u64 t = (u64)a[i] + b[i] + c;
        r[i] = (u32)t;
        c = t >> 32;
    }
    return c;
}

__device__ void add_mod(u32 *r, const u32 *a, const u32 *b) {
    const u32 p[8] = {
        SECP256K1_P0, SECP256K1_P1, SECP256K1_P2, SECP256K1_P3,
        SECP256K1_P4, SECP256K1_P5, SECP256K1_P6, SECP256K1_P7
    };
    u32 c = add(r, a, b);
    u32 mod = 1;
    if (c == 0) {
        for (int i = 7; i >= 0; i--) {
            if (r[i] < p[i]) {
                mod = 0;
                break;
            }
            if (r[i] > p[i]) break;
        }
    }
    if (mod == 1) sub(r, r, p);
}

__device__ void sub_mod(u32 *r, const u32 *a, const u32 *b) {
    const u32 p[8] = { SECP256K1_P0, SECP256K1_P1, SECP256K1_P2, SECP256K1_P3, SECP256K1_P4, SECP256K1_P5, SECP256K1_P6, SECP256K1_P7 };
    u64 borrow = 0;
    for (int i = 0; i < 8; i++) {
        borrow += (u64)a[i];
        borrow -= b[i];
        r[i] = borrow;
        borrow = (borrow >> 32) & 1; // Ограничиваем borrow до 0 или 1
    }
    if (borrow) { // Если результат отрицательный
        u64 carry = 0;
        for (int i = 0; i < 8; i++) {
            carry += (u64)r[i] + p[i];
            r[i] = carry;
            carry >>= 32;
        }
    }
}

// Определение SECP256K1_Q
__constant__ u32 SECP256K1_Q[8] = {
    0xFC632551, 0xF3B9CAC2, 0xA7179E84, 0xBCE6FAAD,
    0xFFFFFFFF, 0xFFFFFFFF, 0x00000000, 0xFFFFFFFF
};

__device__ void mul_mod(u32 *r, const u32 *a, const u32 *b) {
    const u32 p[8] = {
        SECP256K1_P0, SECP256K1_P1, SECP256K1_P2, SECP256K1_P3,
        SECP256K1_P4, SECP256K1_P5, SECP256K1_P6, SECP256K1_P7
    };
    u64 c = 0;
    u32 t[16] = {0};
    for (int i = 0; i < 8; i++) {
        c = 0;
        for (int j = 0; j < 8; j++) {
            c += (u64)a[i] * b[j] + t[i + j];
            t[i + j] = (u32)c;
            c >>= 32;
        }
        t[i + 8] = (u32)c;
    }
    u32 q[8], m[8];
    for (int i = 0; i < 8; i++) q[i] = t[i + 8];
    c = 0;
    for (int i = 0; i < 8; i++) {
        c += (u64)q[i] * SECP256K1_Q[i] + m[i];
        m[i] = (u32)c;
        c >>= 32;
    }
    if (c) {
        u32 c2 = sub(r, t, m);
        if (c2) sub(r, r, p);
    } else {
        sub_mod(r, t, m);
    }
}

__device__ void square_mod(u32 *r, const u32 *a) {
    mul_mod(r, a, a);
}

__device__ void inverse_mod(u32 *r, const u32 *a) {
    const u32 p[8] = { SECP256K1_P0, SECP256K1_P1, SECP256K1_P2, SECP256K1_P3, SECP256K1_P4, SECP256K1_P5, SECP256K1_P6, SECP256K1_P7 };
    u32 u[8], v[8], s[8], t[8];
    for (int i = 0; i < 8; i++) {
        u[i] = a[i];
        v[i] = p[i];
        s[i] = (i == 0) ? 1 : 0;
        t[i] = 0;
    }
    int iteration = 0;
    if (threadIdx.x == 0) {
        printf("inverse_mod: Start with u[0] = %u, v[0] = %u\n", u[0], v[0]);
    }
    while (true) {
        if (threadIdx.x == 0 && iteration % 100 == 0) {
            printf("inverse_mod: Iteration %d, u[0] = %u, v[0] = %u\n", iteration, u[0], v[0]);
        }
        while (!(u[0] & 1)) {
            for (int i = 0; i < 7; i++) u[i] = (u[i] >> 1) | (u[i + 1] << 31);
            u[7] >>= 1;
            if (s[0] & 1) add(s, s, p);
            for (int i = 0; i < 7; i++) s[i] = (s[i] >> 1) | (s[i + 1] << 31);
            s[7] >>= 1;
            if (threadIdx.x == 0 && iteration % 100 == 0) {
                printf("inverse_mod: After u shift, u[0] = %u, s[0] = %u\n", u[0], s[0]);
            }
        }
        while (!(v[0] & 1)) {
            for (int i = 0; i < 7; i++) v[i] = (v[i] >> 1) | (v[i + 1] << 31);
            v[7] >>= 1;
            if (t[0] & 1) add(t, t, p);
            for (int i = 0; i < 7; i++) t[i] = (t[i] >> 1) | (t[i + 1] << 31);
            t[7] >>= 1;
            if (threadIdx.x == 0 && iteration % 100 == 0) {
                printf("inverse_mod: After v shift, v[0] = %u, t[0] = %u\n", v[0], t[0]);
            }
        }
        bool u_zero = true, v_zero = true;
        for (int i = 0; i < 8; i++) {
            if (u[i]) u_zero = false;
            if (v[i]) v_zero = false;
        }
        if (u_zero) {
            if (threadIdx.x == 0) {
                printf("inverse_mod: u is zero, returning t[0] = %u\n", t[0]);
            }
            for (int i = 0; i < 8; i++) r[i] = t[i];
            return;
        }
        if (v_zero) {
            if (threadIdx.x == 0) {
                printf("inverse_mod: v is zero, returning s[0] = %u\n", s[0]);
            }
            for (int i = 0; i < 8; i++) r[i] = s[i];
            return;
        }
        int cmp = 0;
        for (int i = 7; i >= 0; i--) {
            if (u[i] > v[i]) { cmp = 1; break; }
            if (u[i] < v[i]) { cmp = -1; break; }
        }
        if (cmp >= 0) {
            sub_mod(u, u, v);
            sub_mod(s, s, t);
            if (threadIdx.x == 0 && iteration % 100 == 0) {
                printf("inverse_mod: After u -= v, u[0] = %u, s[0] = %u\n", u[0], s[0]);
            }
        } else {
            sub_mod(v, v, u);
            sub_mod(t, t, s);
            if (threadIdx.x == 0 && iteration % 100 == 0) {
                printf("inverse_mod: After v -= u, v[0] = %u, t[0] = %u\n", v[0], t[0]);
            }
        }
        iteration++;
        if (iteration > 10000) {
            if (threadIdx.x == 0) {
                printf("inverse_mod: Too many iterations, aborting\n");
            }
            for (int i = 0; i < 8; i++) r[i] = 0;
            return;
        }
    }
}

__device__ int convert_to_window_naf(u32 *naf, const u32 *k) {
    u32 c = 0;
    int len = 0;
    for (int i = 0; i < 8; i++) {
        c |= k[i];
        naf[i] = k[i];
    }
    if (!c) return 0;
    int i = 0;
    while (i < SECP256K1_NAF_SIZE) {
        if (naf[i] & 1) {
            u32 v = naf[i] & 0x1f;
            if (v > 16) v = v - 32;
            naf[i] = v;
            if (v < 0) {
                c = 1;
                for (int j = i + 1; j < SECP256K1_NAF_SIZE && c; j++) {
                    c += naf[j];
                    naf[j] = c & 0xffffffff;
                    c >>= 32;
                }
            }
            i += 5;
        } else {
            i++;
        }
    }
    for (i = SECP256K1_NAF_SIZE - 1; i >= 0; i--) {
        if (naf[i]) return i;
    }
    return 0;
}

__device__ void point_double(u32 *x1, u32 *y1, u32 *z1) {
    u32 lambda[8], t[8], x[8], y[8], z[8];
    for (int i = 0; i < 8; i++) {
        x[i] = x1[i];
        y[i] = y1[i];
        z[i] = z1[i];
    }
    if (threadIdx.x == 0) {
        printf("point_double: Start with x1[0] = %u, y1[0] = %u, z1[0] = %u\n", x1[0], y1[0], z1[0]);
    }
    square_mod(t, z);
    if (threadIdx.x == 0) {
        printf("point_double: After square_mod(t, z), t[0] = %u\n", t[0]);
    }
    sub_mod(t, x, t);
    add_mod(t, t, x);
    square_mod(lambda, x);
    add_mod(lambda, lambda, lambda);
    add_mod(lambda, lambda, lambda);
    add(t, t, t);
    if (threadIdx.x == 0) {
        printf("point_double: Before inverse_mod, t[0] = %u\n", t[0]);
    }
    inverse_mod(t, t);
    if (threadIdx.x == 0) {
        printf("point_double: After inverse_mod, t[0] = %u\n", t[0]);
    }
    mul_mod(lambda, lambda, t);
    square_mod(t, lambda);
    sub_mod(t, t, x);
    sub_mod(x1, t, x);
    sub_mod(t, x, x1);
    mul_mod(t, lambda, t);
    sub_mod(y1, t, y);
    mul_mod(z1, y, z);
    add(z1, z1, z1);
    if (threadIdx.x == 0) {
        printf("point_double: Finished with x1[0] = %u, y1[0] = %u, z1[0] = %u\n", x1[0], y1[0], z1[0]);
    }
}

__device__ void point_add_xy(u32 *x1, u32 *y1, u32 *z1) {
    const u32 x2[8] = { SECP256K1_GX0, SECP256K1_GX1, SECP256K1_GX2, SECP256K1_GX3, SECP256K1_GX4, SECP256K1_GX5, SECP256K1_GX6, SECP256K1_GX7 };
    const u32 y2[8] = { SECP256K1_GY0, SECP256K1_GY1, SECP256K1_GY2, SECP256K1_GY3, SECP256K1_GY4, SECP256K1_GY5, SECP256K1_GY6, SECP256K1_GY7 };
    u32 t1[8], t2[8], t3[8], t4[8];

    // Если z1 = 0, просто копируем (x2, y2)
    bool z1_zero = true;
    for (int i = 0; i < 8; i++) {
        if (z1[i]) z1_zero = false;
    }
    if (z1_zero) {
        for (int i = 0; i < 8; i++) {
            x1[i] = x2[i];
            y1[i] = y2[i];
            z1[i] = 1;
        }
        return;
    }

    // t1 = z1^2
    square_mod(t1, z1);

    // t2 = x2 * z1^2
    mul_mod(t2, x2, t1);

    // t1 = z1 * t1 (z1^3)
    mul_mod(t1, t1, z1);

    // t3 = y2 * z1^3
    mul_mod(t3, y2, t1);

    // t2 = t2 - x1
    sub_mod(t2, t2, x1);

    // t3 = t3 - y1
    sub_mod(t3, t3, y1);

    // Если t2 = 0 и t3 = 0, точка удваивается
    bool t2_zero = true, t3_zero = true;
    for (int i = 0; i < 8; i++) {
        if (t2[i]) t2_zero = false;
        if (t3[i]) t3_zero = false;
    }
    if (t2_zero && t3_zero) {
        point_double(x1, y1, z1);
        return;
    }

    // t1 = z1 * t2
    mul_mod(t1, z1, t2);

    // t4 = t2^2
    square_mod(t4, t2);

    // t2 = t2 * t4 (t2^3)
    mul_mod(t2, t2, t4);

    // t4 = x1 * t4
    mul_mod(t4, x1, t4);

    // x1 = t3^2 - (t2 + 2 * t4)
    square_mod(x1, t3);
    add_mod(t2, t2, t4);
    add_mod(t2, t2, t4);
    sub_mod(x1, x1, t2);

    // t2 = t4 - x1
    sub_mod(t2, t4, x1);

    // t2 = t3 * t2
    mul_mod(t2, t3, t2);

    // y1 = t2 - t4 * t3
    mul_mod(t4, t4, t3);
    sub_mod(y1, t2, t4);

    // z1 = t1
    for (int i = 0; i < 8; i++) {
        z1[i] = t1[i];
    }

    if (threadIdx.x == 0) {
        printf("point_add_xy: Result x1[0] = %u, y1[0] = %u, z1[0] = %u\n", x1[0], y1[0], z1[0]);
    }
}

__device__ void point_mul_xy(u32 *x1, u32 *y1, const u32 *k) {
    u32 z1[8] = {1, 0, 0, 0, 0, 0, 0, 0};
    if (threadIdx.x == 0) {
        printf("point_mul_xy: Initialized x1[0] = %u, y1[0] = %u\n", x1[0], y1[0]);
        printf("point_mul_xy: Private key k[0] = %u, k[7] = %u\n", k[0], k[7]);
    }
    int started = 0;
    for (int i = 7; i >= 0; i--) {
        for (int j = 31; j >= 0; j--) {
            if (started) point_double(x1, y1, z1);
            if (k[i] & (1u << j)) {
                if (started) point_add_xy(x1, y1, z1);
                else {
                    started = 1;
                    if (threadIdx.x == 0) {
                        printf("point_mul_xy: Started with bit at i=%d, j=%d\n", i, j);
                    }
                }
            }
            if (started && threadIdx.x == 0) {
                printf("point_mul_xy: After iter (i=%d, j=%d), x1[0] = %u, y1[0] = %u\n", i, j, x1[0], y1[0]);
            }
        }
    }
    if (threadIdx.x == 0) {
        printf("point_mul_xy: Before inverse_mod, z1[0] = %u\n", z1[0]);
    }
    inverse_mod(z1, z1);
    if (threadIdx.x == 0) {
        printf("point_mul_xy: After inverse_mod, z1[0] = %u\n", z1[0]);
    }
    mul_mod(y1, y1, z1);
    square_mod(z1, z1);
    mul_mod(x1, x1, z1);
}

__device__ void to_hex_device(const uint8_t *data, size_t len, char *result) {
    const char hex_chars[] = "0123456789abcdef";
    for (size_t i = 0; i < len; i++) {
        result[i * 2] = hex_chars[(data[i] >> 4) & 0x0F];
        result[i * 2 + 1] = hex_chars[data[i] & 0x0F];
    }
}

__device__ void to_checksum_address_device(const uint8_t *address, uint8_t *hash) {
    char addr_hex[40];
    to_hex_device(address, 20, addr_hex);

    char addr_lower[40];
    for (int i = 0; i < 40; i++) {
        addr_lower[i] = (addr_hex[i] >= 'A' && addr_hex[i] <= 'F') ? addr_hex[i] + 32 : addr_hex[i];
    }

    uint8_t hash_lower[32];
    keccak256_get_hash(hash_lower, (const u8*)addr_lower, 40);

    for (int i = 0; i < 20; i++) {
        char hash_hex_char = hash_lower[i / 2];
        int nibble = (i % 2 == 0) ? (hash_hex_char >> 4) : (hash_hex_char & 0x0F);
        if (nibble >= 8 && addr_hex[i * 2] >= 'a' && addr_hex[i * 2] <= 'f') {
            addr_hex[i * 2] -= 32;
        }
    }

    for (int i = 0; i < 20; i++) {
        uint8_t high = (addr_hex[i * 2] >= 'a') ? (addr_hex[i * 2] - 'a' + 10) : (addr_hex[i * 2] - '0');
        uint8_t low = (addr_hex[i * 2 + 1] >= 'a') ? (addr_hex[i * 2 + 1] - 'a' + 10) : (addr_hex[i * 2 + 1] - '0');
        hash[i] = (high << 4) | low;
    }
}

__global__ void generate_wallets(WalletInfo *results, const uint8_t* private_keys, int num_wallets, const secp256k1_t* tmps) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= num_wallets) return;

    if (idx == 0) {
        printf("generate_wallets: Thread 0 started\n");
    }

    uint8_t private_key[32];
    memcpy(private_key, private_keys + idx * 32, 32);

    u32 k[8];
    for (int i = 0; i < 8; i++) {
        k[i] = (private_key[i * 4] << 24) | (private_key[i * 4 + 1] << 16) |
               (private_key[i * 4 + 2] << 8) | private_key[i * 4 + 3];
    }

    u32 pub_x[8], pub_y[8];
    point_mul_xy(pub_x, pub_y, k, tmps);

    if (idx == 0) {
        printf("generate_wallets: Thread 0 finished point_mul_xy, pub_x[0] = %u, pub_y[0] = %u\n", pub_x[0], pub_y[0]);
    }

    WalletInfo &result = results[idx];
    memcpy(result.private_key, private_key, 32);
    for (int i = 0; i < 20; i++) result.address[i] = 0; // Временная заглушка
    result.found = false;
}

std::string to_hex(const uint8_t *data, size_t len) {
    std::string result;
    const char hex_chars[] = "0123456789abcdef";
    for (size_t i = 0; i < len; i++) {
        result += hex_chars[(data[i] >> 4) & 0x0F];
        result += hex_chars[data[i] & 0x0F];
    }
    return result;
}

std::string to_checksum_address(const uint8_t *address) {
    std::string addr_hex = to_hex(address, 20);
    return "0x" + addr_hex;
}

void save_to_file(const std::string &log_path, const std::string &mnemonic, const std::string &address, const std::string &private_key) {
    std::ofstream file(log_path, std::ios::app);
    file << "Seed: " << mnemonic << "\n";
    file << "Address: " << address << "\n";
    file << "Private: 0x" << private_key << "\n";
    file << "-----------------------------\n";
    file.close();
}

bool check_address_in_db(const std::string &db_path, const uint8_t *address) {
    sqlite3 *db;
    if (sqlite3_open(db_path.c_str(), &db) != SQLITE_OK) return false;
    std::string query = "SELECT 1 FROM addresses WHERE address = ?";
    sqlite3_stmt *stmt;
    sqlite3_prepare_v2(db, query.c_str(), -1, &stmt, nullptr);
    sqlite3_bind_blob(stmt, 1, address, 20, SQLITE_STATIC);
    bool found = sqlite3_step(stmt) == SQLITE_ROW;
    sqlite3_finalize(stmt);
    sqlite3_close(db);
    return found;
}

int main() {
    std::string num_threads_str, db_path, log_path;
    std::cout << "Введите желаемое количество потоков (минимум 2): ";
    std::getline(std::cin, num_threads_str);
    int num_threads = std::stoi(num_threads_str);
    std::cout << "Введите путь к базе данных: ";
    std::getline(std::cin, db_path);
    std::cout << "Введите путь к файлу log.txt: ";
    std::getline(std::cin, log_path);

    int threads_per_block = 256;
    int blocks = (num_threads + threads_per_block - 1) / threads_per_block;
    int num_wallets = blocks * threads_per_block;

    cudaDeviceProp prop;
    CUDA_CHECK(cudaGetDeviceProperties(&prop, 0));
    std::cout << "Используется GPU: " << prop.name << "\n";
    std::cout << "Запуск с " << blocks << " блоками и " << threads_per_block << " потоками на блок, всего " << num_wallets << " кошельков\n";

    secp256k1_t tmps_host;
    tmps_host.xy[0] = SECP256K1_G_PRE_COMPUTED_00;
    tmps_host.xy[1] = SECP256K1_G_PRE_COMPUTED_01;
    tmps_host.xy[2] = SECP256K1_G_PRE_COMPUTED_02;
    tmps_host.xy[3] = SECP256K1_G_PRE_COMPUTED_03;
    tmps_host.xy[4] = SECP256K1_G_PRE_COMPUTED_04;
    tmps_host.xy[5] = SECP256K1_G_PRE_COMPUTED_05;
    tmps_host.xy[6] = SECP256K1_G_PRE_COMPUTED_06;
    tmps_host.xy[7] = SECP256K1_G_PRE_COMPUTED_07;
    tmps_host.xy[8] = SECP256K1_G_PRE_COMPUTED_08;
    tmps_host.xy[9] = SECP256K1_G_PRE_COMPUTED_09;
    tmps_host.xy[10] = SECP256K1_G_PRE_COMPUTED_10;
    tmps_host.xy[11] = SECP256K1_G_PRE_COMPUTED_11;
    tmps_host.xy[12] = SECP256K1_G_PRE_COMPUTED_12;
    tmps_host.xy[13] = SECP256K1_G_PRE_COMPUTED_13;
    tmps_host.xy[14] = SECP256K1_G_PRE_COMPUTED_14;
    tmps_host.xy[15] = SECP256K1_G_PRE_COMPUTED_15;
    tmps_host.xy[16] = SECP256K1_G_PRE_COMPUTED_16;
    tmps_host.xy[17] = SECP256K1_G_PRE_COMPUTED_17;
    tmps_host.xy[18] = SECP256K1_G_PRE_COMPUTED_18;
    tmps_host.xy[19] = SECP256K1_G_PRE_COMPUTED_19;
    tmps_host.xy[20] = SECP256K1_G_PRE_COMPUTED_20;
    tmps_host.xy[21] = SECP256K1_G_PRE_COMPUTED_21;
    tmps_host.xy[22] = SECP256K1_G_PRE_COMPUTED_22;
    tmps_host.xy[23] = SECP256K1_G_PRE_COMPUTED_23;
    tmps_host.xy[24] = SECP256K1_G_PRE_COMPUTED_24;
    tmps_host.xy[25] = SECP256K1_G_PRE_COMPUTED_25;
    tmps_host.xy[26] = SECP256K1_G_PRE_COMPUTED_26;
    tmps_host.xy[27] = SECP256K1_G_PRE_COMPUTED_27;
    tmps_host.xy[28] = SECP256K1_G_PRE_COMPUTED_28;
    tmps_host.xy[29] = SECP256K1_G_PRE_COMPUTED_29;
    tmps_host.xy[30] = SECP256K1_G_PRE_COMPUTED_30;
    tmps_host.xy[31] = SECP256K1_G_PRE_COMPUTED_31;
    tmps_host.xy[32] = SECP256K1_G_PRE_COMPUTED_32;
    tmps_host.xy[33] = SECP256K1_G_PRE_COMPUTED_33;
    tmps_host.xy[34] = SECP256K1_G_PRE_COMPUTED_34;
    tmps_host.xy[35] = SECP256K1_G_PRE_COMPUTED_35;
    tmps_host.xy[36] = SECP256K1_G_PRE_COMPUTED_36;
    tmps_host.xy[37] = SECP256K1_G_PRE_COMPUTED_37;
    tmps_host.xy[38] = SECP256K1_G_PRE_COMPUTED_38;
    tmps_host.xy[39] = SECP256K1_G_PRE_COMPUTED_39;
    tmps_host.xy[40] = SECP256K1_G_PRE_COMPUTED_40;
    tmps_host.xy[41] = SECP256K1_G_PRE_COMPUTED_41;
    tmps_host.xy[42] = SECP256K1_G_PRE_COMPUTED_42;
    tmps_host.xy[43] = SECP256K1_G_PRE_COMPUTED_43;
    tmps_host.xy[44] = SECP256K1_G_PRE_COMPUTED_44;
    tmps_host.xy[45] = SECP256K1_G_PRE_COMPUTED_45;
    tmps_host.xy[46] = SECP256K1_G_PRE_COMPUTED_46;
    tmps_host.xy[47] = SECP256K1_G_PRE_COMPUTED_47;
    tmps_host.xy[48] = SECP256K1_G_PRE_COMPUTED_48;
    tmps_host.xy[49] = SECP256K1_G_PRE_COMPUTED_49;
    tmps_host.xy[50] = SECP256K1_G_PRE_COMPUTED_50;
    tmps_host.xy[51] = SECP256K1_G_PRE_COMPUTED_51;
    tmps_host.xy[52] = SECP256K1_G_PRE_COMPUTED_52;
    tmps_host.xy[53] = SECP256K1_G_PRE_COMPUTED_53;
    tmps_host.xy[54] = SECP256K1_G_PRE_COMPUTED_54;
    tmps_host.xy[55] = SECP256K1_G_PRE_COMPUTED_55;
    tmps_host.xy[56] = SECP256K1_G_PRE_COMPUTED_56;
    tmps_host.xy[57] = SECP256K1_G_PRE_COMPUTED_57;
    tmps_host.xy[58] = SECP256K1_G_PRE_COMPUTED_58;
    tmps_host.xy[59] = SECP256K1_G_PRE_COMPUTED_59;
    tmps_host.xy[60] = SECP256K1_G_PRE_COMPUTED_60;
    tmps_host.xy[61] = SECP256K1_G_PRE_COMPUTED_61;
    tmps_host.xy[62] = SECP256K1_G_PRE_COMPUTED_62;
    tmps_host.xy[63] = SECP256K1_G_PRE_COMPUTED_63;
    tmps_host.xy[64] = SECP256K1_G_PRE_COMPUTED_64;
    tmps_host.xy[65] = SECP256K1_G_PRE_COMPUTED_65;
    tmps_host.xy[66] = SECP256K1_G_PRE_COMPUTED_66;
    tmps_host.xy[67] = SECP256K1_G_PRE_COMPUTED_67;
    tmps_host.xy[68] = SECP256K1_G_PRE_COMPUTED_68;
    tmps_host.xy[69] = SECP256K1_G_PRE_COMPUTED_69;
    tmps_host.xy[70] = SECP256K1_G_PRE_COMPUTED_70;
    tmps_host.xy[71] = SECP256K1_G_PRE_COMPUTED_71;
    tmps_host.xy[72] = SECP256K1_G_PRE_COMPUTED_72;
    tmps_host.xy[73] = SECP256K1_G_PRE_COMPUTED_73;
    tmps_host.xy[74] = SECP256K1_G_PRE_COMPUTED_74;
    tmps_host.xy[75] = SECP256K1_G_PRE_COMPUTED_75;
    tmps_host.xy[76] = SECP256K1_G_PRE_COMPUTED_76;
    tmps_host.xy[77] = SECP256K1_G_PRE_COMPUTED_77;
    tmps_host.xy[78] = SECP256K1_G_PRE_COMPUTED_78;
    tmps_host.xy[79] = SECP256K1_G_PRE_COMPUTED_79;
    tmps_host.xy[80] = SECP256K1_G_PRE_COMPUTED_80;
    tmps_host.xy[81] = SECP256K1_G_PRE_COMPUTED_81;
    tmps_host.xy[82] = SECP256K1_G_PRE_COMPUTED_82;
    tmps_host.xy[83] = SECP256K1_G_PRE_COMPUTED_83;
    tmps_host.xy[84] = SECP256K1_G_PRE_COMPUTED_84;
    tmps_host.xy[85] = SECP256K1_G_PRE_COMPUTED_85;
    tmps_host.xy[86] = SECP256K1_G_PRE_COMPUTED_86;
    tmps_host.xy[87] = SECP256K1_G_PRE_COMPUTED_87;
    tmps_host.xy[88] = SECP256K1_G_PRE_COMPUTED_88;
    tmps_host.xy[89] = SECP256K1_G_PRE_COMPUTED_89;
    tmps_host.xy[90] = SECP256K1_G_PRE_COMPUTED_90;
    tmps_host.xy[91] = SECP256K1_G_PRE_COMPUTED_91;
    tmps_host.xy[92] = SECP256K1_G_PRE_COMPUTED_92;
    tmps_host.xy[93] = SECP256K1_G_PRE_COMPUTED_93;
    tmps_host.xy[94] = SECP256K1_G_PRE_COMPUTED_94;
    tmps_host.xy[95] = SECP256K1_G_PRE_COMPUTED_95;

    secp256k1_t *tmps_device;
    std::cout << "Выделение памяти для tmps_device\n";
    CUDA_CHECK(cudaMalloc(&tmps_device, sizeof(secp256k1_t)));
    std::cout << "Копирование tmps_host на tmps_device\n";
    CUDA_CHECK(cudaMemcpy(tmps_device, &tmps_host, sizeof(secp256k1_t), cudaMemcpyHostToDevice));

    std::vector<std::string> mnemonics(num_wallets);
    std::vector<uint8_t> seeds(num_wallets * 64);
    std::vector<uint8_t> private_keys(num_wallets * 32);
    for (int i = 0; i < num_wallets; i++) {
        mnemonics[i] = generate_mnemonic();
        mnemonic_to_seed(mnemonics[i], seeds.data() + i * 64);
        memcpy(private_keys.data() + i * 32, seeds.data() + i * 64, 32);
    }

    WalletInfo *d_results;
    uint8_t *d_private_keys;
    std::cout << "Выделение памяти для d_results: " << num_wallets * sizeof(WalletInfo) << " байт\n";
    CUDA_CHECK(cudaMalloc(&d_results, num_wallets * sizeof(WalletInfo)));
    std::cout << "Выделение памяти для d_private_keys: " << num_wallets * 32 << " байт\n";
    CUDA_CHECK(cudaMalloc(&d_private_keys, num_wallets * 32));
    std::cout << "Копирование private_keys на d_private_keys\n";
    CUDA_CHECK(cudaMemcpy(d_private_keys, private_keys.data(), num_wallets * 32, cudaMemcpyHostToDevice));

    std::cout << "Запуск ядра generate_wallets\n";
    generate_wallets<<<blocks, threads_per_block>>>(d_results, d_private_keys, num_wallets, tmps_device);
    CUDA_CHECK(cudaGetLastError());
    std::cout << "Синхронизация после ядра\n";
    CUDA_CHECK(cudaDeviceSynchronize());

    std::vector<WalletInfo> h_results(num_wallets);
    std::cout << "Копирование результатов с устройства на хост\n";
    CUDA_CHECK(cudaMemcpy(h_results.data(), d_results, num_wallets * sizeof(WalletInfo), cudaMemcpyDeviceToHost));

    std::vector<std::future<void>> futures;
    for (int i = 0; i < num_wallets; i++) {
        std::string address_hex = to_checksum_address(h_results[i].address);
        std::string private_hex = to_hex(h_results[i].private_key, 32);
        std::cout << i + 1 << ": Address: " << address_hex << "\n";

        if (check_address_in_db(db_path, h_results[i].address)) {
            futures.push_back(std::async(std::launch::async, save_to_file, log_path, mnemonics[i], address_hex, private_hex));
        }
    }

    for (auto &f : futures) f.wait();

    CUDA_CHECK(cudaFree(d_results));
    CUDA_CHECK(cudaFree(d_private_keys));
    CUDA_CHECK(cudaFree(tmps_device));
    return 0;
}
