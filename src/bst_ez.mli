(** Lock-free Binary Search Tree.

  {b Warning}: This implementation doesn't account for duplicate keys. 

  {b Sources}: This implementation is based on the following research paper by Arunmoezhi Ramachandran and Neeraj Mittal

  Link to the paper: https://dl.acm.org/doi/10.1145/2684464.2684472  *)

(** {1 API}*)

type 'elt t 
(** The type of a Binary Search Tree, containing keys of type ['elt] *)

val create : compare:('elt -> 'elt -> int) -> unit -> 'elt t 
(** [create ~compare ()] creates a new empty Binary Search Tree where the keys are sorted based on the given [compare] function. *)

val add : 'elt t -> 'elt -> unit 
(** [insert tree key] inserts a new key into Binary Search Tree [tree] if the key doesn't already exist in the tree. If the key is already present then the operation is ignored. *)

val find : 'elt t -> 'elt -> bool 
(** [find tree key] checks whether [key] exists in the Binary Search Tree [tree]. Returns [true] if it exists and [false] otherwise. *)

val remove : 'elt t -> 'elt -> bool 
(** [remove tree key] tries to remove the [key] from the Binary Search Tree [tree].Returns [true] on successful removal and [false] if the Binary Search Tree does not contain the [key]. *)

val to_list : 'elt t -> 'elt list 
(** [to_list tree] returns the list of keys present in the Binary Search Tree [tree]. The returned ['elt list] contains the keys in the inorder fashion or sorted fashion according to the Binary Search tree's [tree] compare function. *)

(* val to_plist : 'elt t -> ('elt * int) list

val adddbg : 'elt t -> 'elt -> ('elt -> unit) -> unit  *)

val print_tree : 'elt t -> ('elt -> unit) -> unit 