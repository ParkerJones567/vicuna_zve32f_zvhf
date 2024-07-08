# Copyright TU Wien
# Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


    .text
    .global main
main:
    la              a0, vdata_start
    addi a1, a0, 32

    li              t0, 16
    vsetvli         t0, t0, e16,m2,tu,mu
    
        
    vle16.v          v2, (a0)
    vle16.v          v4, (a1)
    
    vrem.vv          v0, v2, v4
    
    vse16.v          v0, (a0)
   
  

    la              a0, vdata_start
    la              a1, vdata_end
    j               spill_cache


    .data
    .align 10
    .global vdata_start
    .global vdata_end
vdata_start:
    .word 0x002d0002 # 45 | 2               #V2 start
    .word 0x012dff8f # 301 | -113
    .word 0x0fa4fc0c # 4004 | -1012
    .word 0x1f400002 # 8000 | 2
    .word 0x002d0002 # 45 | 2
    .word 0x012dff8f # 301 | -113
    .word 0x0fa4fc0c # 4004 | -1012
    .word 0x1f400002 # 8000 | 2             #V2 end
    .word 0x000a0003 # 10 | 3               #V4 start
    .word 0xfffd0019 # -3 | 25
    .word 0x0005ffce # 5 | -50
    .word 0x03e80002 # 1000 | 2
    .word 0x000a0003 # 10 | 3
    .word 0xfffd0019 # -3 | 25
    .word 0x0005ffce # 5 | -50
    .word 0x03e80002 # 1000 | 2             #V4 end
vdata_end:

    .align 10
    .global vref_start
    .global vref_end
vref_start:
    .word 0x00050002 # 5 | 2                #V0 start
    .word 0x0001fff3 # 1 | -13
    .word 0x0004fff4 # 4 | -12
    .word 0x00000000 # 0 | 0
    .word 0x00050002 # 5 | 2
    .word 0x0001fff3 # 1 | -13
    .word 0x0004fff4 # 4 | -12
    .word 0x00000000 # 0 | 0                #V0 end
    .word 0x000a0003 
    .word 0xfffd0019 
    .word 0x0005ffce 
    .word 0x03e80002 
    .word 0x000a0003 
    .word 0xfffd0019 
    .word 0x0005ffce 
    .word 0x03e80002 
vref_end:
