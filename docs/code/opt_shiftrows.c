#include <stdint.h>
#include <riscv_vector.h>

vint8m4_t aes_shiftrows(vint8m4_t vec) {
    // Permutation index vector: 0 5 10 15 4 9 14 3 8 13 2 7 12 1 6 11

    // prepare masks (should be done in initialization step)
    uint16_t msk1  = 0x1111,
             msk2  = 0x3333,
             msk3  = 0x7777,
             msk4  = 0xEC80;
    vbool2_t vmsk1 = __riscv_vlm_v_b2((uint8_t *)&msk1, 16),
             vmsk2 = __riscv_vlm_v_b2((uint8_t *)&msk2, 16),
             vmsk3 = __riscv_vlm_v_b2((uint8_t *)&msk3, 16),
             vmsk4 = __riscv_vlm_v_b2((uint8_t *)&msk4, 16);

    // perform the permutation
    vint8m4_t tmp;
    vbool2_t msk;
    tmp = __riscv_vmv_v_x_i8m4(0, 16);
    tmp = __riscv_vslideup_vx_i8m4(tmp, vec, 4, 16);
    msk = __riscv_vmnot_m_b2(vmsk3, 16);
    vec = __riscv_vslidedown_vx_i8m4_m(msk, vec, 4, 16);
    tmp = __riscv_vslideup_vx_i8m4_m(vmsk3, tmp, tmp, 4, 16);
    msk = __riscv_vmnot_m_b2(vmsk2, 16);
    vec = __riscv_vslidedown_vx_i8m4_m(msk, vec, 4, 16);
    tmp = __riscv_vslideup_vx_i8m4_m(vmsk2, tmp, tmp, 4, 16);
    msk = __riscv_vmnot_m_b2(vmsk1, 16);
    vec = __riscv_vslidedown_vx_i8m4_m(msk, vec, 4, 16);
    return __riscv_vmerge_vvm_i8m4(vec, tmp, vmsk4, 16);
}
