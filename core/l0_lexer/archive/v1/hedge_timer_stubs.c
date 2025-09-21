/*
 * Event-driven hedge timer stubs - kqueue (macOS) / timerfd (Linux)
 * Integrates with existing v25_R1 system
 */

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/fail.h>

#ifdef __APPLE__
#include <sys/event.h>
#include <sys/time.h>
#include <unistd.h>

// macOS kqueue implementation
value hedge_timer_setup_macos_stub(value unit) {
    CAMLparam1(unit);
    int kq = kqueue();
    if (kq == -1) {
        caml_failwith("kqueue creation failed");
    }
    CAMLreturn(Val_int(kq));
}

value hedge_timer_arm_stub(value v_kq, value v_ns) {
    CAMLparam2(v_kq, v_ns);
    int kq = Int_val(v_kq);
    int64_t ns = Int64_val(v_ns);
    
    struct kevent kev;
    // Convert nanoseconds to milliseconds for timer
    int64_t ms = ns / 1000000;
    if (ms <= 0) ms = 1; // minimum 1ms
    
    EV_SET(&kev, 1, EVFILT_TIMER, EV_ADD | EV_ONESHOT, 0, ms, NULL);
    
    if (kevent(kq, &kev, 1, NULL, 0, NULL) == -1) {
        caml_failwith("kevent arm failed");
    }
    
    CAMLreturn(Val_unit);
}

value hedge_timer_disarm_stub(value v_kq) {
    CAMLparam1(v_kq);
    int kq = Int_val(v_kq);
    
    struct kevent kev;
    EV_SET(&kev, 1, EVFILT_TIMER, EV_DELETE, 0, 0, NULL);
    kevent(kq, &kev, 1, NULL, 0, NULL); // Ignore errors for disarm
    
    CAMLreturn(Val_unit);
}

#else
// Linux timerfd implementation (simplified stub)
#include <sys/timerfd.h>
#include <time.h>

value hedge_timer_setup_macos_stub(value unit) {
    CAMLparam1(unit);
    int fd = timerfd_create(CLOCK_MONOTONIC, TFD_NONBLOCK);
    if (fd == -1) {
        caml_failwith("timerfd creation failed");
    }
    CAMLreturn(Val_int(fd));
}

value hedge_timer_arm_stub(value v_fd, value v_ns) {
    CAMLparam2(v_fd, v_ns);
    int fd = Int_val(v_fd);
    int64_t ns = Int64_val(v_ns);
    
    struct itimerspec timer;
    timer.it_value.tv_sec = ns / 1000000000;
    timer.it_value.tv_nsec = ns % 1000000000;
    timer.it_interval.tv_sec = 0;
    timer.it_interval.tv_nsec = 0;
    
    if (timerfd_settime(fd, 0, &timer, NULL) == -1) {
        caml_failwith("timerfd arm failed");
    }
    
    CAMLreturn(Val_unit);
}

value hedge_timer_disarm_stub(value v_fd) {
    CAMLparam1(v_fd);
    int fd = Int_val(v_fd);
    
    struct itimerspec timer;
    timer.it_value.tv_sec = 0;
    timer.it_value.tv_nsec = 0;
    timer.it_interval.tv_sec = 0;
    timer.it_interval.tv_nsec = 0;
    
    timerfd_settime(fd, 0, &timer, NULL); // Ignore errors for disarm
    
    CAMLreturn(Val_unit);
}

#endif