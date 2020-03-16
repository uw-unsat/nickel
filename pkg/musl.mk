MUSL            := pkg/musl
USER_CFLAGS     += -I $(MUSL)/arch/$(ARCH) -I $(MUSL)/arch/generic -I $(MUSL)/include
MUSL_CFLAGS     := -I include/uapi/musl/internal -I $(MUSL)/src/internal $(USER_CFLAGS) -w

$(O)/$(MUSL)/%.o: CFLAGS := $(MUSL_CFLAGS)

include/uapi/bits/alltypes.h: $(MUSL)/arch/$(ARCH)/bits/alltypes.h.in $(MUSL)/include/alltypes.h.in
	$(Q)$(MKDIR_P) $(@D)
	$(Q)sed -f $(MUSL)/tools/mkalltypes.sed $^ > $@~
	$(QUIET_GEN)mv $@~ $@

include/uapi/bits/syscall.h: $(MUSL)/arch/$(ARCH)/bits/syscall.h.in
	$(Q)$(MKDIR_P) $(@D)
	$(Q)cp $< $@~
	$(Q)sed -n -e s/__NR_/SYS_/p < $< >> $@~
	$(QUIET_GEN)mv $@~ $@

include/uapi/musl/internal/version.h: $(MUSL)/VERSION
	$(Q)$(MKDIR_P) $(@D)
	$(Q)printf '#define VERSION "%s"\n' "$$(cat $<)" > $@~
	$(QUIET_GEN)mv $@~ $@

# Don't include the following files:
# - anything about /etc/passwd (pulling in too much)
# - ldso/dynlink.c (using OS-specific dynamic linker)
# - src/env/__init_tls.c (using OS-specific TLS)

MUSL_SRCS       := \
        $(wildcard $(MUSL)/src/ctype/*.c) \
        $(wildcard $(MUSL)/src/dirent/*.c) \
        $(filter-out %/__init_tls.c,$(wildcard $(MUSL)/src/env/*.c)) \
        $(MUSL)/src/errno/__errno_location.c \
        $(MUSL)/src/errno/strerror.c \
        $(MUSL)/src/exit/abort.c \
        $(MUSL)/src/exit/assert.c \
        $(MUSL)/src/exit/atexit.c \
        $(MUSL)/src/exit/exit.c \
        $(MUSL)/src/exit/_Exit.c \
        $(wildcard $(MUSL)/src/fcntl/*.c) \
        $(MUSL)/src/internal/floatscan.c \
        $(MUSL)/src/internal/intscan.c \
        $(MUSL)/src/internal/libc.c \
        $(MUSL)/src/internal/shgetc.c \
        $(MUSL)/src/internal/syscall.c \
        $(MUSL)/src/internal/syscall_ret.c \
        $(MUSL)/src/internal/procfdname.c \
        $(MUSL)/src/internal/version.c \
        $(MUSL)/src/ldso/dlclose.c \
        $(MUSL)/src/ldso/dlerror.c \
        $(MUSL)/src/ldso/dlopen.c \
        $(MUSL)/src/ldso/dlsym.c \
        $(MUSL)/src/ldso/__dlsym.c \
        $(MUSL)/src/legacy/getpagesize.c \
        $(MUSL)/src/linux/utimes.c \
        $(wildcard $(MUSL)/src/locale/*.c) \
        $(MUSL)/src/malloc/aligned_alloc.c \
        $(MUSL)/src/malloc/__brk.c \
        $(MUSL)/src/malloc/calloc.c \
        $(MUSL)/src/malloc/expand_heap.c \
        $(MUSL)/src/malloc/malloc.c \
        $(MUSL)/src/malloc/memalign.c \
        $(MUSL)/src/malloc/posix_memalign.c \
        $(MUSL)/src/math/$(ARCH)/sqrt.s \
        $(MUSL)/src/math/$(ARCH)/fabs.s \
        $(MUSL)/src/math/$(ARCH)/fmodl.s \
        $(MUSL)/src/math/copysignl.c \
        $(MUSL)/src/math/__fpclassifyl.c \
        $(MUSL)/src/math/frexpl.c \
        $(MUSL)/src/math/ldexp.c \
        $(MUSL)/src/math/scalbn.c \
        $(MUSL)/src/math/scalbnl.c \
        $(MUSL)/src/math/__signbitl.c \
        $(MUSL)/src/misc/basename.c \
        $(MUSL)/src/misc/dirname.c \
        $(MUSL)/src/misc/ioctl.c \
        $(MUSL)/src/misc/getopt.c \
        $(MUSL)/src/misc/getopt_long.c \
        $(MUSL)/src/misc/getpriority.c \
        $(MUSL)/src/misc/setpriority.c \
        $(MUSL)/src/misc/uname.c \
        $(MUSL)/src/prng/rand_r.c \
        $(wildcard $(MUSL)/src/mman/*.c) \
        $(wildcard $(MUSL)/src/multibyte/*.c) \
        $(MUSL)/src/process/execl.c \
        $(MUSL)/src/process/execlp.c \
        $(MUSL)/src/process/execv.c \
        $(MUSL)/src/process/execve.c \
        $(MUSL)/src/process/execvp.c \
        $(MUSL)/src/process/fork.c \
        $(MUSL)/src/process/wait.c \
        $(MUSL)/src/process/waitpid.c \
        $(wildcard $(MUSL)/src/regex/*.c) \
        $(MUSL)/src/search/hsearch.c \
        $(MUSL)/src/select/select.c \
        $(MUSL)/src/setjmp/$(ARCH)/longjmp.s \
        $(MUSL)/src/setjmp/$(ARCH)/setjmp.s \
        $(MUSL)/src/signal/block.c \
        $(MUSL)/src/signal/raise.c \
        $(MUSL)/src/signal/restore.c \
        $(MUSL)/src/signal/setitimer.c \
        $(MUSL)/src/signal/sigaction.c \
        $(MUSL)/src/signal/sigemptyset.c \
        $(MUSL)/src/signal/siglongjmp.c \
        $(MUSL)/src/signal/signal.c \
        $(wildcard $(MUSL)/src/stat/*.c) \
        $(MUSL)/src/stdio/asprintf.c \
        $(MUSL)/src/stdio/dprintf.c \
        $(MUSL)/src/stdio/fclose.c \
        $(MUSL)/src/stdio/__fdopen.c \
        $(MUSL)/src/stdio/feof.c \
        $(MUSL)/src/stdio/ferror.c \
        $(MUSL)/src/stdio/fflush.c \
        $(MUSL)/src/stdio/fgetc.c \
        $(MUSL)/src/stdio/fgets.c \
        $(MUSL)/src/stdio/fileno.c \
        $(MUSL)/src/stdio/flockfile.c \
        $(MUSL)/src/stdio/__fmodeflags.c \
        $(MUSL)/src/stdio/funlockfile.c \
        $(MUSL)/src/stdio/fopen.c \
        $(MUSL)/src/stdio/fprintf.c \
        $(MUSL)/src/stdio/fputc.c \
        $(MUSL)/src/stdio/fputs.c \
        $(MUSL)/src/stdio/fread.c \
        $(MUSL)/src/stdio/fscanf.c \
        $(MUSL)/src/stdio/fseek.c \
        $(MUSL)/src/stdio/ftell.c \
        $(MUSL)/src/stdio/ftrylockfile.c \
        $(MUSL)/src/stdio/fwrite.c \
        $(MUSL)/src/stdio/getc.c \
        $(MUSL)/src/stdio/getdelim.c \
        $(MUSL)/src/stdio/getline.c \
        $(MUSL)/src/stdio/__lockfile.c \
        $(MUSL)/src/stdio/ofl.c \
        $(MUSL)/src/stdio/ofl_add.c \
        $(MUSL)/src/stdio/__overflow.c \
        $(MUSL)/src/stdio/perror.c \
        $(MUSL)/src/stdio/printf.c \
        $(MUSL)/src/stdio/putc.c \
        $(MUSL)/src/stdio/putchar.c \
        $(MUSL)/src/stdio/puts.c \
        $(MUSL)/src/stdio/remove.c \
        $(MUSL)/src/stdio/rename.c \
        $(MUSL)/src/stdio/rewind.c \
        $(MUSL)/src/stdio/setvbuf.c \
        $(MUSL)/src/stdio/snprintf.c \
        $(MUSL)/src/stdio/sprintf.c \
        $(MUSL)/src/stdio/sscanf.c \
        $(MUSL)/src/stdio/stderr.c \
        $(MUSL)/src/stdio/stdin.c \
        $(MUSL)/src/stdio/__stdio_close.c \
        $(MUSL)/src/stdio/__stdio_exit.c \
        $(MUSL)/src/stdio/__stdio_read.c \
        $(MUSL)/src/stdio/__stdio_seek.c \
        $(MUSL)/src/stdio/__stdio_write.c \
        $(MUSL)/src/stdio/stdout.c \
        $(MUSL)/src/stdio/__stdout_write.c \
        $(MUSL)/src/stdio/__string_read.c \
        $(MUSL)/src/stdio/__toread.c \
        $(MUSL)/src/stdio/__towrite.c \
        $(MUSL)/src/stdio/__uflow.c \
        $(MUSL)/src/stdio/ungetc.c \
        $(MUSL)/src/stdio/vasprintf.c \
        $(MUSL)/src/stdio/vdprintf.c \
        $(MUSL)/src/stdio/vfprintf.c \
        $(MUSL)/src/stdio/vfscanf.c \
        $(MUSL)/src/stdio/vprintf.c \
        $(MUSL)/src/stdio/vsnprintf.c \
        $(MUSL)/src/stdio/vsprintf.c \
        $(MUSL)/src/stdio/vsscanf.c \
        $(MUSL)/src/stdlib/abs.c \
        $(MUSL)/src/stdlib/atof.c \
        $(MUSL)/src/stdlib/atoi.c \
        $(MUSL)/src/stdlib/atol.c \
        $(MUSL)/src/stdlib/atoll.c \
        $(MUSL)/src/stdlib/bsearch.c \
        $(MUSL)/src/stdlib/labs.c \
        $(MUSL)/src/stdlib/qsort.c \
        $(MUSL)/src/stdlib/strtod.c \
        $(MUSL)/src/stdlib/strtol.c \
        $(wildcard $(MUSL)/src/string/*.c) \
        $(MUSL)/src/termios/tcgetattr.c \
        $(MUSL)/src/termios/tcsetattr.c \
        $(MUSL)/src/thread/$(ARCH)/clone.s \
        $(MUSL)/src/thread/__lock.c \
        $(MUSL)/src/thread/pthread_cleanup_push.c \
        $(MUSL)/src/thread/pthread_setcancelstate.c \
        $(MUSL)/src/thread/pthread_testcancel.c \
        $(wildcard $(MUSL)/src/thread/sem_*.c) \
        $(MUSL)/src/thread/synccall.c \
        $(MUSL)/src/thread/__syscall_cp.c \
        $(MUSL)/src/thread/__timedwait.c \
        $(MUSL)/src/thread/__wait.c \
        $(MUSL)/src/time/clock_gettime.c \
        $(MUSL)/src/time/gettimeofday.c \
        $(MUSL)/src/time/localtime.c \
        $(MUSL)/src/time/localtime_r.c \
        $(MUSL)/src/time/__map_file.c \
        $(MUSL)/src/time/mktime.c \
        $(MUSL)/src/time/__month_to_secs.c \
        $(MUSL)/src/time/nanosleep.c \
        $(MUSL)/src/time/__secs_to_tm.c \
        $(MUSL)/src/time/strftime.c \
        $(MUSL)/src/time/strptime.c \
        $(MUSL)/src/time/time.c \
        $(MUSL)/src/time/__tm_to_secs.c \
        $(MUSL)/src/time/__tz.c \
        $(MUSL)/src/time/__year_to_secs.c \
        $(wildcard $(MUSL)/src/unistd/*.c) \

MUSL_LDSO_SRCS  := \
        $(MUSL)/ldso/dlstart.c \

MUSL_OBJS       := $(call object,$(MUSL_SRCS))
MUSL_LDSO_OBJS  := $(call object,$(MUSL_LDSO_SRCS))
