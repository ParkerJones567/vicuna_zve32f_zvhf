# Copyright TU Wien
# Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


    .text
    .global main
main:
    la              a0, vdata_start
    addi a1, a0, 32
    
    li              t0, 8
    li              t1, 4
    vsetvli         t0, t0, e32,m2,tu,mu
    
        
    vle32.v          v2, (a0)
    
    vremu.vx          v0, v2, t1
    
    vse32.v          v0, (a0)
   
  

    la              a0, vdata_start
    la              a1, vdata_end
    j               spill_cache


    .data
    .align 10
    .global vdata_start
    .global vdata_end
vdata_start:
    .int           0
    .int           2
    .int           4
    .int           6
    .int           -2
    .int           -4
    .int           -6
    .int           -8
vdata_end:

    .align 10
    .global vref_start
    .global vref_end
vref_start:
    .int           0
    .int           2
    .int           0
    .int           2
    .int           2
    .int           0
    .int           2
    .int           0
vref_end:
