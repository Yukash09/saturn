(** Sequential and Parallel model-based tests of BST *)
open QCheck
open STM
module Bst_ez = Saturn.Bst_ez

module Lib_spec : Spec = struct 
  module IntOrd = struct 
    type t = int 
    let compare = Int.compare 
  end

  module S = Set.Make(IntOrd)

  type state = S.t 

  let init_state = S.empty 

  type sut = int Bst_ez.t

  let init_sut () = Bst_ez.create ~compare:Int.compare ()

  let cleanup _ = () 

  type cmd = 
    | Add of int 
    (* | Find of int 
    | Remove of int  *)
  
  let show_cmd cmd = 
    match cmd with 
      | Add i -> Printf.sprintf "Adding %d\n" i 
      (* | Find i -> Printf.sprintf "Searching for %d\n" i 
      | Remove i -> Printf.sprintf "Removing %d" i *)

  let run cmd (t : sut) = 
    match cmd with 
      | Add i -> Res (unit , Bst_ez.add t i)
      (* | Find i -> Res (bool , Bst_ez.find t i)
      | Remove i -> Res (bool , Bst_ez.remove t i) *)

  let next_state (cmd : cmd) (curr_state : state) = 
    match cmd with 
      | Add i -> S.add i curr_state 
      (* | Find _ -> curr_state 
      | Remove i -> S.remove i curr_state *)

  let precond _cmd _state = true 

  let postcond (cmd : cmd) (curr_state : state) (res : res) = 
    match cmd , res with 
      | Add _ , Res((Unit , _) , _) -> true 
      (* | Find i , Res((Bool , _) , b) -> 
        b = begin match S.find_opt i curr_state with 
              | Some _ -> true 
              | None -> false
            end
      | Remove _ , Res((Bool , _) , _) -> true  *)
      | _ -> false 

  let arb_cmd (state : state) =
    let gen = let cardinality = S.cardinal state in 
    if cardinality < 1000 then Gen.int 
    else Gen.(oneof [oneof_list (S.to_list state) ; int]) in 
    QCheck.make ~print:show_cmd 
    (QCheck.Gen.oneof
      [
        Gen.map (fun i -> Add i) gen ;
        (* Gen.map (fun i -> Find i) gen ;
        Gen.map (fun i -> Remove i) gen ; *)
      ]
    )
end

let () = Stm_run.run ~name:"Saturn.Bst_ez" (module Lib_spec) |> exit

