#include "terminate_benchmark.h"

void benchmark_success()
{
    __asm__ volatile("jalr x0, 124(x0)");     //jump to 0x7c to signal success (Custom use interrupt, will not be called)
    
}

void benchmark_failure()
{
    __asm__ volatile("jalr x0, 120(x0)");   //jump to 0x78 to signal failure(all other interrupts also funnel here)
}
