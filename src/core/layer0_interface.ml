(** Layer 0 Interface Module
    
    This module provides the proper interface structure for L0 components
    so that L1 can reference them correctly.
*)

(* Re-export L0_v25 as a submodule *)
module L0_v25 = struct
  include L0_v25
end