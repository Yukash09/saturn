module Bst = Bst 
module Atomic = Dscheck.TracedAtomic
(** This is needed in this order as the bst.ml file contains
    {[
      module Atomic = Multicore_magic.Transparent_atomic
    ]}
    which is in multicore-magic-dscheck library only a subset of
    [Dscheck.TracedAtomic] function. *)

let insert_insert () = 
  Atomic.trace (fun () ->
    let bst = Bst.create ~compare:Int.compare () in 
    let total = 4  in 
    Atomic.spawn (fun () -> 
      for i = 1 to total do 
        Bst.add bst i ;
      done) ;

    Atomic.spawn (fun () ->
      for i = total + 1 to 2*total do
        Bst.add bst i ;
      done) ;
    
    Atomic.final (fun () -> 
      let items = Bst.to_list bst in 
      
      Atomic.check (fun () ->
        List.length items = 2*total) (* Check for total count *);
      Atomic.check (fun () ->
        List.sort Int.compare items = items) (* Check for sortedness *);
      Atomic.check (fun () ->
        List.sort_uniq Int.compare items = items) (* Check for unique keys *);
    )
  )

let insert_insert_duplicates () = 
  Atomic.trace (fun () ->
    let bst = Bst.create ~compare:Int.compare () in 
    let total = 8 in 
    (* Domain 1 inserts - 1 ; 2 ; 3 ; 4 ; 5 
       Domain 2 inserts - 3 ; 4 ; 5 ; 6 ; 7 ; 8 *)
    Atomic.spawn (fun () ->
      for i = 1 to total - 3 do
        Bst.add bst i ;
      done) ;
    Atomic.spawn (fun () ->
      for i = 3 to total do
        Bst.add bst i
      done) ;

    Atomic.final (fun () -> 
      let items = Bst.to_list bst in 
      Atomic.check (fun () ->
        List.length items = total) (* Check for total count *);
      Atomic.check (fun () ->
        List.sort Int.compare items = items) (* Check for sortedness *);
      Atomic.check (fun () ->
        List.sort_uniq Int.compare items = items) (* Check for unique keys *);
    )
  )

let insert_search () = 
  Atomic.trace (fun () -> 
    let _bst = Bst.create ~compare:Int.compare () in 
    let total = 4 in 
    (* Domain 1 inserts - 1 , 2 , ... , 2*total 
       Domain 2 searches - 3 , ... , 2*total + 3 *)

    Atomic.spawn (fun () ->
      for i = 1 to 2*total do () done)
  )

let () = 
  let open Alcotest in 
  run "DSCheck_Bst"
    [
      ( "basic",
        [
          test_case "2-disjoint-insert" `Slow insert_insert ;
          test_case "2-insert-duplicates" `Slow insert_insert_duplicates ;
        ]
      ) ;
    ]