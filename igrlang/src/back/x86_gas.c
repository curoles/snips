#include <stdio.h>

void x86_gen_function(
    FILE* out
    //Symbol f,
    //calee[],
    //caller[]
)
{
    fprintf(out, ".file \"todo.igr.s\"\n");
    //prologue
    //
    fprintf(out, "fun_name:\n");
    //fprintf(out, "pushl %%ebx\n");
    //fprintf(out, "pushl %%esi\n");
    //fprintf(out, "pushl %%edi\n");

    // Save EBP on stack.
    fprintf(out, "pushl %%ebp\n");

    // move the value of ESP into EBP
    fprintf(out, "movl %%esp, %%ebp\n");

//sub    $0x10,%esp 16 bytes on stack

    // The C calling convention is to store return values in EAX when exiting a routine.
    fprintf(out, "movl $0, %%eax\n");

    // Free the space saved on the stack by copying EBP into ESP,
    // then popping the saved value of EBP back to EBP.
    fprintf(out, "leave\n");

    // Return control to the calling procedure by popping
    // the saved instruction pointer from the stack.
    fprintf(out, "ret\n");
}
