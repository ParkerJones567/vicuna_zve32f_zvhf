#include <stdint.h>
#include <riscv_vector.h>
#include <uart.h>

int8_t array[16] __attribute__ ((aligned (4))) = {
    1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16
};

int main(void) {
    
    uart_printf("Hello World from Vicuna!\n");
    int8_t target[sizeof(array)], *src = array, *dst = target;
    size_t vl;
    for (int n = sizeof(array); n > 0; n -= vl, src += vl, dst += vl) {
        vl            = __riscv_vsetvl_e8m1(n);
        vint8m1_t vec = __riscv_vle8_v_i8m1(src, vl);
        vec           = __riscv_vmul_vx_i8m1(vec, 5, vl);
        vec           = __riscv_vadd_vx_i8m1(vec, 7, vl);
        __riscv_vse8_v_i8m1(dst, vec, vl);
    }
    for (int i = 0; i < sizeof(array); i++) {
        uart_printf("%d * 5 + 7 = %d\n", array[i], target[i]);
    }
    __asm__ volatile("jalr x0, 124(x0)"); // jump to address 7C(ends simulation)
    return 0;
}
