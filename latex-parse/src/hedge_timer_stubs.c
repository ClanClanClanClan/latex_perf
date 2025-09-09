#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/unixsupport.h>
#include <caml/threads.h>
#include <stdint.h>
#include <unistd.h>

#if defined(__APPLE__)
  #include <sys/event.h>
  #include <sys/time.h>

  CAMLprim value ocaml_ht_create(value unit){
    int kq = kqueue(); if (kq < 0) uerror("kqueue", Nothing); return Val_int(kq);
  }
  CAMLprim value ocaml_ht_arm_ns(value vkq, value vns){
    int kq = Int_val(vkq); int64_t ns = Int64_val(vns);
    struct kevent kev;
    EV_SET(&kev, 1, EVFILT_TIMER, EV_ADD | EV_ONESHOT, 0, (int)(ns/1000000LL), NULL);
    if (kevent(kq, &kev, 1, NULL, 0, NULL) < 0) uerror("kevent(timer)", Nothing);
    return Val_unit;
  }
  CAMLprim value ocaml_ht_wait2(value vkq, value vfd1, value vfd2){
    CAMLparam3(vkq, vfd1, vfd2);
    int kq  = Int_val(vkq);
    int fd1 = Int_val(vfd1);
    int fd2 = Int_val(vfd2);
    struct kevent kevset[2]; int nset=0;
    if (fd1 >= 0) { EV_SET(&kevset[nset++], fd1, EVFILT_READ, EV_ADD|EV_ENABLE, 0, 0, NULL); }
    if (fd2 >= 0) { EV_SET(&kevset[nset++], fd2, EVFILT_READ, EV_ADD|EV_ENABLE, 0, 0, NULL); }
    if (nset>0)  { if (kevent(kq, kevset, nset, NULL, 0, NULL) < 0) uerror("kevent(add)", Nothing); }
    struct kevent out[3];
    caml_enter_blocking_section();
      int nev = kevent(kq, NULL, 0, out, 3, NULL);
    caml_leave_blocking_section();
    if (nev < 0) uerror("kevent(wait)", Nothing);
    int timer_fired = 0; int which = -1;
    for (int i=0;i<nev;i++){
      if (out[i].filter == EVFILT_TIMER) timer_fired = 1;
      if (out[i].filter == EVFILT_READ){
        if (fd1 >= 0 && (int)out[i].ident == fd1) which = fd1;
        else if (fd2 >= 0 && (int)out[i].ident == fd2) which = fd2;
      }
    }
    value t = caml_alloc_tuple(2);
    Store_field(t,0, Val_int(timer_fired));
    Store_field(t,1, Val_int(which));
    CAMLreturn(t);
  }
#else
  #include <sys/timerfd.h>
  #include <sys/epoll.h>
  CAMLprim value ocaml_ht_create(value unit){
    int ep = epoll_create1(EPOLL_CLOEXEC); if (ep<0) uerror("epoll_create1", Nothing); return Val_int(ep);
  }
  CAMLprim value ocaml_ht_arm_ns(value vep, value vns){
    int ep = Int_val(vep); int tfd = timerfd_create(CLOCK_MONOTONIC, TFD_CLOEXEC);
    if (tfd < 0) uerror("timerfd_create", Nothing);
    struct itimerspec its = {0}; int64_t ns = Int64_val(vns);
    its.it_value.tv_sec = ns/1000000000LL; its.it_value.tv_nsec = ns%1000000000LL;
    if (timerfd_settime(tfd, 0, &its, NULL)<0) uerror("timerfd_settime", Nothing);
    struct epoll_event ev = { .events = EPOLLIN, .data.fd = tfd };
    if (epoll_ctl(ep, EPOLL_CTL_ADD, tfd, &ev) < 0) uerror("epoll_ctl(timer)", Nothing);
    return Val_unit;
  }
  CAMLprim value ocaml_ht_wait2(value vep, value vfd1, value vfd2){
    CAMLparam3(vep, vfd1, vfd2);
    int ep = Int_val(vep);
    int fd1 = Int_val(vfd1);
    int fd2 = Int_val(vfd2);
    struct epoll_event ev1 = { .events = EPOLLIN, .data.fd = fd1 };
    struct epoll_event ev2 = { .events = EPOLLIN, .data.fd = fd2 };
    if (fd1 >= 0) epoll_ctl(ep, EPOLL_CTL_ADD, fd1, &ev1);
    if (fd2 >= 0) epoll_ctl(ep, EPOLL_CTL_ADD, fd2, &ev2);
    struct epoll_event out;
    caml_enter_blocking_section();
      int n = epoll_wait(ep, &out, 1, -1);
    caml_leave_blocking_section();
    if (n<0) uerror("epoll_wait", Nothing);
    int timer_fired = 0; int which = -1;
    if (out.data.fd == fd1) which = fd1;
    else if (out.data.fd == fd2) which = fd2;
    else timer_fired = 1;
    value t = caml_alloc_tuple(2);
    Store_field(t,0, Val_int(timer_fired));
    Store_field(t,1, Val_int(which));
    CAMLreturn(t);
  }
#endif