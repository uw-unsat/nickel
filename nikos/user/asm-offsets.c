#include <io/kbuild.h>
  
enum {
#define __SYSCALL(x) SYS_##x,
#include <mcertikos/syscall.inc>
#undef __SYSCALL
};

int main(void)
{
#define __SYSCALL(x) DEFINE(SYS_##x, SYS_##x);
#include <mcertikos/syscall.inc>
#undef __SYSCALL

        return 0;
}
