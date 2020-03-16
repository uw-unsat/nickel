#include <nistar/syscall.h>
#include <stdnoreturn.h>
#include <sys/resource.h>
#include <sys/wait.h>

/* current self / proc / env */
usymlink_t self_get_process_container();
usymlink_t self_get_internal_container();
void self_set_env_containers(usymlink_t process_container, usymlink_t internal_container);
void self_set_process_container(usymlink_t process_container);
void self_set_internal_container(usymlink_t internal_container);
noreturn void hs_exit(int status);
long hs_wait4(usymlink_t usym, int *wstatus, int options, struct rusage *rusage, usymlink_t *ret);
