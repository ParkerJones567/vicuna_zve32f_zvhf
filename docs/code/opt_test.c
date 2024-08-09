#include <stdint.h>
#include <riscv_vector.h>
#include <uart.h>

#include <opt_reduction.c>
#include <opt_shiftrows.c>
#include <opt_vlse.c>

int8_t array[16] __attribute__ ((aligned (4))) = {
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15
};

//vint8m1_t vload_stride_4(int8_t *addr, size_t vl);
static int test_opt_vlse(void) {
    vint8m1_t v1, v2, tmp, sum;
    vbool8_t neq;
    size_t vl;
    vl  = __riscv_vsetvl_e8m1(sizeof(array) / 4);
    v1  = vload_stride_4(array, vl);
    v2  = __riscv_vlse8_v_i8m1(array, 4, vl);

    // compare v1 and v2
    neq = __riscv_vmsne_vv_i8m1_b8(v1, v2, vl);
    tmp = __riscv_vmv_v_x_i8m1(0, vl);
    tmp = __riscv_vmerge_vxm_i8m1(tmp, 1, neq, vl);
    sum = __riscv_vmv_v_x_i8m1(0, 1);
    sum = __riscv_vredsum_vs_i8m1_i8m1(sum, tmp, vl);
    return __riscv_vmv_x_s_i8m1_i8(sum);
}

//int8_t sum_reduce(vint8m1_t vec, size_t vl);
static int test_opt_reduction(void) {
    vint8m1_t vec, sum;
    size_t vl;
    vl  = __riscv_vsetvl_e8m1(sizeof(array));
    vec = __riscv_vle8_v_i8m1(array, vl);
    sum = __riscv_vmv_v_x_i8m1(0, vl);
    sum = __riscv_vredsum_vs_i8m1_i8m1(sum, vec, vl);
    int8_t ref = __riscv_vmv_x_s_i8m1_i8(sum);
    return ref != sum_reduce(vec, vl);
}

//vint8m4_t aes_shiftrows(vint8m4_t vec);
static int test_opt_shiftrows(void) {
    int8_t ref[16] = { 0, 5, 10, 15, 4, 9, 14, 3, 8, 13, 2, 7, 12, 1, 6, 11 };
    vint8m4_t v1, v2, tmp;
    vbool2_t neq;
    vint8m1_t sum;
    size_t vl;
    vl  = __riscv_vsetvl_e8m4(16);
    v1  = __riscv_vle8_v_i8m4(array, vl);
    v1  = aes_shiftrows(v1);
    v2  = __riscv_vle8_v_i8m4(ref, vl);

    // compare v1 and v2
    neq = __riscv_vmsne_vv_i8m4_b2(v1, v2, vl);
    tmp = __riscv_vmv_v_x_i8m4(0, vl);
    tmp = __riscv_vmerge_vxm_i8m4(tmp, 1, neq, vl);
    sum = __riscv_vmv_v_x_i8m1(0, 1);
    sum = __riscv_vredsum_vs_i8m4_i8m1(tmp, sum, vl);
    return __riscv_vmv_x_s_i8m1_i8(sum);
}

static int (*test_funcs[])(void) = {
    test_opt_vlse,
    test_opt_reduction,
    test_opt_shiftrows
};
static const char *test_names[] = {
    "optimized strided vector load",
    "optimized sum reduction",
    "optimized AES shiftrows"
};

int main(void) {
    uart_printf("Starting tests\n");
    for (int i = 0; i < sizeof(test_funcs) / sizeof(void *); i++) {
        int ret = test_funcs[i]();
        if (ret == 0) {
            uart_printf("[PASS] %s\n", test_names[i]);
        } else {
            uart_printf("[FAIL] %s function returned %d\n", test_names[i], ret);
        }
    }
    uart_printf("Tests complete\n");
    asm volatile("jr x0");
    return 0;
}
