(** Facade re-exporting all public modules of the [l0_lexer] library.

    Downstream code (e.g. [latex-parse]) refers to modules through
    [Latex_parse_lib.Config], [Latex_parse_lib.Broker], etc. *)

module Config : module type of Config
module Clock : module type of Clock
module Hedge_timer : module type of Hedge_timer
module Mlock : module type of Mlock
module Meminfo : module type of Meminfo
module Gc_prep : module type of Gc_prep
module Pretouch : module type of Pretouch
module Arena : module type of Arena
module Ipc : module type of Ipc
module Catcode : module type of Catcode
module Simd_guard : module type of Simd_guard
module Real_processor : module type of Real_processor
module Worker : module type of Worker
module Broker : module type of Broker
module Service_bracket : module type of Service_bracket
module Main_service : module type of Runtime_main_service
module Runtime_main_service : module type of Runtime_main_service
module Metrics_prometheus : module type of Metrics_prometheus
module Fault_injection : module type of Fault_injection
module Barrier : module type of Barrier
module Percentiles : module type of Percentiles
module Alloc_guard : module type of Alloc_guard
module Fast_hash : module type of Fast_hash
