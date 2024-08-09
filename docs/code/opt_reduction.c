#include <stdint.h>
#include <riscv_vector.h>

int8_t sum_reduce(vint8m1_t vec, size_t vl) {
    while (vl > 8) {
        vint8m1_t tmp;
        tmp = __riscv_vslidedown_vx_i8m1(vec, vl / 2, vl);
        vl /= 2;
        vec = __riscv_vadd_vv_i8m1(vec, tmp, vl);
    }
    vint8m1_t sum = __riscv_vmv_v_x_i8m1(0, vl);
    sum = __riscv_vredsum_vs_i8m1_i8m1(sum, vec, vl);
    return __riscv_vmv_x_s_i8m1_i8(sum);
}
