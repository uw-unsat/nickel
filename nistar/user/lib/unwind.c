/*
 * A simple libunwind.
 */

#define _GNU_SOURCE 1
#include <stdint.h>
#include <unwind.h>

struct _Unwind_Context {
        uint64_t ra;
};

_Unwind_Reason_Code _Unwind_Backtrace(_Unwind_Trace_Fn trace, void *data)
{
        uint64_t *fp;

        for (fp = __builtin_frame_address(0); fp; fp = (uint64_t *)fp[0]) {
                struct _Unwind_Context context = { .ra = fp[1] };
                _Unwind_Reason_Code code;

                code = trace(&context, data);
                if (code != _URC_NO_REASON)
                        return code;
        }

        return _URC_NO_REASON;
}

unsigned long _Unwind_GetIPInfo(struct _Unwind_Context *context, int *ip_before_insn)
{
        *ip_before_insn = 0;
        return context->ra;
}
