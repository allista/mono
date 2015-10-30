/*
 * mini-posix.c: POSIX signal handling support for Mono.
 *
 * Authors:
 *   Mono Team (mono-list@lists.ximian.com)
 *
 * Copyright 2001-2003 Ximian, Inc.
 * Copyright 2003-2008 Ximian, Inc.
 *
 * See LICENSE for licensing information.
 */
#include <config.h>
#include <signal.h>
#include <math.h>

#include <mono/metadata/assembly.h>
#include <mono/metadata/loader.h>
#include <mono/metadata/tabledefs.h>
#include <mono/metadata/class.h>
#include <mono/metadata/object.h>
#include <mono/metadata/tokentype.h>
#include <mono/metadata/tabledefs.h>
#include <mono/metadata/threads.h>
#include <mono/metadata/appdomain.h>
#include <mono/metadata/debug-helpers.h>
#include <mono/io-layer/io-layer.h>
#include "mono/metadata/profiler.h"
#include <mono/metadata/profiler-private.h>
#include <mono/metadata/mono-config.h>
#include <mono/metadata/environment.h>
#include <mono/metadata/mono-debug.h>
#include <mono/metadata/gc-internal.h>
#include <mono/metadata/threads-types.h>
#include <mono/metadata/verify.h>
#include <mono/metadata/verify-internals.h>
#include <mono/metadata/mempool-internals.h>
#include <mono/metadata/attach.h>
#include <mono/utils/mono-math.h>
#include <mono/utils/mono-compiler.h>
#include <mono/utils/mono-counters.h>
#include <mono/utils/mono-logger.h>
#include <mono/utils/mono-mmap.h>
#include <mono/utils/dtrace.h>

#include "mini.h"
#include <string.h>
#include <ctype.h>
#include "trace.h"
#include "version.h"

#include "jit-icalls.h"

gboolean win32_chained_exception_needs_run;

void
mono_runtime_install_handlers (void)
{
#ifndef MONO_CROSS_COMPILE
	win32_seh_init();
	win32_seh_set_handler(SIGFPE, mono_sigfpe_signal_handler);
	win32_seh_set_handler(SIGILL, mono_sigill_signal_handler);
	win32_seh_set_handler(SIGSEGV, mono_sigsegv_signal_handler);
	if (mini_get_debug_options ()->handle_sigint)
		win32_seh_set_handler(SIGINT, mono_sigint_signal_handler);
#endif
}

void
mono_runtime_cleanup_handlers (void)
{
#ifndef MONO_CROSS_COMPILE
	win32_seh_cleanup();
#endif
}


/* mono_chain_signal:
 *
 *   Call the original signal handler for the signal given by the arguments, which
 * should be the same as for a signal handler. Returns TRUE if the original handler
 * was called, false otherwise.
 */
gboolean
SIG_HANDLER_SIGNATURE (mono_chain_signal)
{
	win32_chained_exception_needs_run = TRUE;
	return TRUE;
}

#if defined(__i386__) || defined(__x86_64__)
#define FULL_STAT_PROFILER_BACKTRACE 1
#define CURRENT_FRAME_GET_BASE_POINTER(f) (* (gpointer*)(f))
#define CURRENT_FRAME_GET_RETURN_ADDRESS(f) (* (((gpointer*)(f)) + 1))
#if MONO_ARCH_STACK_GROWS_UP
#define IS_BEFORE_ON_STACK <
#define IS_AFTER_ON_STACK >
#else
#define IS_BEFORE_ON_STACK >
#define IS_AFTER_ON_STACK <
#endif
#else
#define FULL_STAT_PROFILER_BACKTRACE 0
#endif

static HANDLE win32_main_thread;
static MMRESULT win32_timer;
static MonoDomain *win32_main_domain;
static MonoJitTlsData *win32_jit_tls;

static void CALLBACK
win32_time_proc (UINT uID, UINT uMsg, DWORD dwUser, DWORD dw1, DWORD dw2)
{
	int call_chain_depth = mono_profiler_stat_get_call_chain_depth ();
	CONTEXT context;

	if (win32_main_domain != mono_get_root_domain ())
		return;

	/* Suspend is required to get consistent data. However, while the thread
	   is suspended, calling any functions that allocate memory can deadlock. */
	if (SuspendThread (win32_main_thread) < 0)
		return;

	context.ContextFlags = CONTEXT_CONTROL;
	if (GetThreadContext (win32_main_thread, &context)) {
		guchar *ips[MONO_PROFILER_MAX_STAT_CALL_CHAIN_DEPTH+1];

#ifdef _WIN64
		ips[0] = (guchar *) context.Rip;
#else
		ips[0] = (guchar *) context.Eip;
#endif

		if (call_chain_depth == 0) {
			ResumeThread (win32_main_thread);
			mono_profiler_stat_hit (ips[0], &context);
		} else {
			int current_frame_index = 1;

#if FULL_STAT_PROFILER_BACKTRACE
			guchar *stack_bottom = (guchar *) win32_jit_tls->end_of_stack;
#ifdef _WIN64
			guchar *stack_top = (guchar *) context.Rsp;
			guchar *current_frame = (guchar *) context.Rbp;
#else
			guchar *stack_top = (guchar *) context.Esp;
			guchar *current_frame = (guchar *) context.Ebp;
#endif

			__try {
				while ((current_frame_index <= call_chain_depth) &&
						(stack_bottom IS_BEFORE_ON_STACK (guchar*) current_frame) &&
						((guchar*) current_frame IS_BEFORE_ON_STACK stack_top)) {
					ips [current_frame_index] = CURRENT_FRAME_GET_RETURN_ADDRESS (current_frame);
					current_frame_index ++;
					stack_top = current_frame;
					current_frame = CURRENT_FRAME_GET_BASE_POINTER (current_frame);
				}
			} __except (GetExceptionCode() == EXCEPTION_ACCESS_VIOLATION) {
				/* Apparently we ended up going through the bottom of the stack - ignore */
			}
#endif

			ResumeThread (win32_main_thread);
			mono_profiler_stat_call_chain (current_frame_index, & ips [0], &context);
		}
	} else {
		ResumeThread (win32_main_thread);
	}
}

void
mono_runtime_setup_stat_profiler (void)
{
	static int inited = 0;
	TIMECAPS timecaps;

	if (inited)
		return;

	win32_main_domain = mono_domain_get ();
	if (win32_main_domain != mono_get_root_domain ())
		return;

	win32_jit_tls = TlsGetValue (mono_jit_tls_id);
	if (win32_jit_tls == NULL)
		return;

	inited = 1;
	if (timeGetDevCaps (&timecaps, sizeof (timecaps)) != TIMERR_NOERROR)
		return;

	if ((win32_main_thread = OpenThread (READ_CONTROL | THREAD_GET_CONTEXT | THREAD_SUSPEND_RESUME, FALSE, GetCurrentThreadId ())) == NULL)
		return;

	if (timeBeginPeriod (1) != TIMERR_NOERROR)
		return;

	if ((win32_timer = timeSetEvent (1, 0, win32_time_proc, 0, TIME_PERIODIC)) == 0) {
		timeEndPeriod (1);
		return;
	}
}

void
mono_runtime_shutdown_stat_profiler (void)
{
}

#ifndef MONO_CROSS_COMPILE

typedef struct
{
	guint32 free_stack;
	MonoContext initial_ctx;
	MonoContext ctx;
} MonoWin32StackOverflowData;

gboolean win32_stack_overflow_walk (StackFrameInfo *frame, MonoContext *ctx, gpointer data)
{
	MonoWin32StackOverflowData* walk_data = (MonoWin32StackOverflowData*)data;

	if (!frame->ji) {
		g_warning ("Exception inside function without unwind info");
		g_assert_not_reached ();
	}

	if (frame->ji != (gpointer)-1) {
		walk_data->free_stack = (guint8*)(MONO_CONTEXT_GET_BP (ctx)) - (guint8*)(MONO_CONTEXT_GET_BP (&walk_data->initial_ctx));
	} else {
		g_warning ("Exception inside function without unwind info");
		g_assert_not_reached ();
	}

	walk_data->ctx = *ctx;

	return !(walk_data->free_stack < 64 * 1024 && frame->ji != (gpointer) -1);
}

extern void (*restore_stack) (void *);

/* Special hack to workaround the fact that the
 * when the SEH handler is called the stack is
 * to small to recover.
 *
 * Stack walking part of this method is from mono_handle_exception
 *
 * The idea is simple; 
 *  - walk the stack to free some space (64k)
 *  - set esp to new stack location
 *  - call mono_arch_handle_exception with stack overflow exception
 *  - set esp to SEH handlers stack
 *  - done
 */
void 
win32_handle_stack_overflow (EXCEPTION_POINTERS* ep, MonoContext *ctx) 
{
	MonoDomain *domain = mono_domain_get ();
	MonoJitInfo rji;
	MonoJitInfo *ji;
	MonoJitTlsData *jit_tls = TlsGetValue (mono_jit_tls_id);
	MonoLMF *lmf = jit_tls->lmf;
	StackFrameInfo frame;
	MonoWin32StackOverflowData stack_overflow_data;

	/* Let's walk the stack to recover
	 * the needed stack space (if possible)
	 */
	memset (&rji, 0, sizeof (rji));
	memset (&stack_overflow_data, 0, sizeof (stack_overflow_data));
	
	ji = mono_jit_info_table_find (domain, MONO_CONTEXT_GET_IP(ctx));

	stack_overflow_data.initial_ctx = *ctx;

	/* try to free 64kb from our stack */
	mono_jit_walk_stack_from_ctx_in_thread (win32_stack_overflow_walk, domain, ctx, FALSE, mono_thread_current (), lmf, &stack_overflow_data);
	
	/* convert into sigcontext to be used in mono_arch_handle_exception */
	mono_arch_monoctx_to_sigctx (&(stack_overflow_data.ctx), ctx);

	/* the new stack-guard page is installed in mono_handle_exception_internal using _resetstkoflw */

	/* use the new stack and call mono_arch_handle_exception () */
	restore_stack (ctx);
}

#endif

