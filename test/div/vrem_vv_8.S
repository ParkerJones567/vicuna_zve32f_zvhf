# Copyright TU Wien
# Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


    .text
    .global main
main:
    la              a0, vdata_start
    addi a1, a0, 32

    li              t0, 32
    vsetvli         t0, t0, e8,m2,tu,mu
    
        
    vle8.v          v2, (a0)
    vle8.v          v4, (a1)
    
    vrem.vv          v0, v2, v4
    
    vse8.v          v0, (a0)
   
  

    la              a0, vdata_start
    la              a1, vdata_end
    j               spill_cache


    .data
    .align 10
    .global vdata_start
    .global vdata_end
vdata_start:
    .word 0x658f2d02 # 101 | -113 | 45 | 2      #V2 start
    .word 0x2c02589a # 44 | 2 | 88 | -102
    .word 0x658f2d02 # 101 | -113 | 45 | 2
    .word 0x2c02589a # 44 | 2 | 88 | -102
    .word 0x658f2d02 # 101 | -113 | 45 | 2
    .word 0x2c02589a # 44 | 2 | 88 | -102
    .word 0x658f2d02 # 101 | -113 | 45 | 2
    .word 0x2c02589a # 44 | 2 | 88 | -102       #V2 end
    .word 0xfc190a03 # -4 | 25 | 10 | 3         #V4 start
    .word 0x0b0205ce # 11 | 2 | 5 | -50
    .word 0xfc190a03 # -4 | 25 | 10 | 3
    .word 0x0b0205ce # 11 | 2 | 5 | -50
    .word 0xfc190a03 # -4 | 25 | 10 | 3
    .word 0x0b0205ce # 11 | 2 | 5 | -50
    .word 0xfc190a03 # -4 | 25 | 10 | 3
    .word 0x0b0205ce # 11 | 2 | 5 | -50         #V4 end
vdata_end:

    .align 10
    .global vref_start
    .global vref_end
vref_start:
    .word 0x01f30502 # 1 | -13 | 5 | 2          #V0 start
    .word 0x000003fe # 0 | 0 | 3 | -2
    .word 0x01f30502 # 1 | -13 | 5 | 2
    .word 0x000003fe # 0 | 0 | 3 | -2
    .word 0x01f30502 # 1 | -13 | 5 | 2
    .word 0x000003fe # 0 | 0 | 3 | -2
    .word 0x01f30502 # 1 | -13 | 5 | 2
    .word 0x000003fe # 0 | 0 | 3 | -2           #V0 end
    .word 0xfc190a03 
    .word 0x0b0205ce 
    .word 0xfc190a03 
    .word 0x0b0205ce 
    .word 0xfc190a03 
    .word 0x0b0205ce 
    .word 0xfc190a03 
    .word 0x0b0205ce 
vref_end:
