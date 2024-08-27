#include "terminate_benchmark.h"

void benchmark_success()
{
    __asm__ volatile("jalr x0, 124(x0)");     //jump to 0x7c to signal success (Custom use interrupt, will not be called)
    
}

void benchmark_failure()
{
    __asm__ volatile("jalr x0, 120(x0)");   //jump to 0x78 to signal failure caused by mismatched test output  Other interrupts are caught by 0x74 to signal a problem
}

void start_cycle_count()
{
    return; //TODO: Use this to signal the beginning of the cycle count
}
