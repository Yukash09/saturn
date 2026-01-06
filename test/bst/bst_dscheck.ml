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
    let bst = Bst.create ~compare:Int.compare () in 
    let total = 4 in 
    (* Domain 1 inserts - 1 , 2 , ... , 2*total 
       Domain 2 searches - 3 , ... , 2*total + 3 *)

    Atomic.spawn (fun () ->
      for i = 1 to 2*total do
        Bst.add bst i
      done) ;

    let found = ref [] in 
    Atomic.spawn (fun () ->
      for i = 3 to (2*total + 3) do 
        if Bst.find bst i then 
          found := i :: !found
      done) ;
    
    Atomic.final (fun () -> 
      let items = Bst.to_list bst in 
      Atomic.check (fun () ->
        List.length items = 2*total) (* Check for total count *);
      Atomic.check (fun () ->
        List.sort Int.compare items = items) (* Check for sortedness *);
      Atomic.check (fun () ->
        List.sort_uniq Int.compare items = items) (* Check for unique keys *);
      Atomic.check (fun () ->
        List.for_all (fun k -> List.mem k items) !found) 
    )
  )

let insert_insert_balanced () = 
  Atomic.trace(fun () -> 
    let bst = Bst.create ~compare:Int.compare () in 
    let keys1 = [|50 ; 30 ; 70 ; 40 ; 20 ; 60 ; 80 ; 10|] in
    let keys2 = [|55 ; 35 ; 65 ; 45 ; 25 ; 65 ; 85 ; 15 |] in (* 65 is duplicate *)
    let siz = 8 in 

    (*Domain 1 adds keys from keys1 , Domain 2 adds keys from keys2 *)
    Atomic.spawn (fun () ->
      for i = 0 to siz - 1 do 
        Bst.add bst keys1.(i) ;
        (* Printf.printf "Adding %d\n%!" keys1.(i) *)
      done) ;
    Atomic.spawn (fun () ->
      for i = 0 to siz - 1 do
        Bst.add bst keys2.(i) ;
        (* Printf.printf "Adding %d\n%!" keys2.(i) *)
      done) ;

    Atomic.final (fun () -> 
      let items = Bst.to_list bst in 
      Atomic.check (fun () ->
        List.length items = 2*siz - 1) (* Check for total count *);
      Atomic.check (fun () ->
        List.sort Int.compare items = items) (* Check for sortedness *);
      Atomic.check (fun () ->
        List.sort_uniq Int.compare items = items) (* Check for unique keys *);
    )
  )

let insert_search_balanced () =
  Atomic.trace(fun () -> 
    let bst = Bst.create ~compare:Int.compare () in 
    let keys1 = [|50 ; 30 ; 70 ; 40 ; 20 ; 60 ; 80 ; 10|] in
    let siz = 8 in 

    (*Domain 1 adds keys from keys1 , Domain 2 searches for keys from keys1 *)
    Atomic.spawn (fun () ->
      for i = 0 to siz - 1 do 
        Bst.add bst keys1.(i) ;
        (* Printf.printf "Adding %d\n%!" keys1.(i) *)
      done) ;
    let found = ref [] in 
    Atomic.spawn (fun () ->
      for i = 0 to siz-1 do 
        if Bst.find bst keys1.(i) then 
          found := keys1.(i) :: !found
      done) ;

    Atomic.final (fun () -> 
      let items = Bst.to_list bst in 
      Atomic.check (fun () ->
        let _ = List.iter (fun x -> Printf.printf "%d " x) !found in List.length items = siz) (* Check for total count *);
      Atomic.check (fun () ->
        List.sort Int.compare items = items) (* Check for sortedness *);
      Atomic.check (fun () ->
        List.sort_uniq Int.compare items = items) (* Check for unique keys *);
      Atomic.check (fun () ->
        List.for_all (fun k -> List.mem k items) !found) 
    )
  )

let insert_remove () = 
  Atomic.trace (fun () -> 
    let bst = Bst.create ~compare:Int.compare () in 
    let total = 6 in

    Atomic.spawn (fun () ->
      for i = 1 to total - 2 do
        Bst.add bst i ;
      done ;
      Bst.add bst 5 ;
      Bst.add bst 6) ;

    let removed = ref [] in 
    Atomic.spawn (fun () -> 
      for i = 1 to total do 
        if Bst.remove bst i then 
          removed := !removed @ [i]
      done ; 
      if Bst.remove bst 5 then removed := !removed @ [5]  ;
      if Bst.remove bst 5 then removed := !removed @ [6]  ;) ;
    
    Atomic.final (fun () -> 
      let items = Bst.to_list bst in 
      Atomic.check(fun () ->
        List.length items + List.length !removed = total) ; 
      Atomic.check(fun () -> 
        List.sort Int.compare items = items) ;
      Atomic.check(fun () -> 
        List.for_all (fun k -> not (Bst.find bst k)) (!removed))
    )
  )

let insert_remove_search_balanced () = 
  Atomic.trace (fun () ->
    let bst = Bst.create ~compare:Int.compare () in 
    let keys1 = [|50 ; 30 ; 70 ; 40 ; 20 ; 60 ; 80 ; 10|] in 
    let siz = 8 in 

    (* Domain 1 adds keys , Domain 2 searches keys , Domain 3 removes keys *)
    Atomic.spawn (fun () ->
      for i = 0 to siz - 1 do
        Bst.add bst keys1.(i)
      done) ;
    
    let found = ref [] in 
    Atomic.spawn (fun () -> 
      for i = 0 to siz - 1 do
        if Bst.find bst keys1.(i) then found := !found @ [keys1.(i)]
      done) ;

    let removed = ref [] in 
    Atomic.spawn (fun () -> 
      for i = 0 to siz - 1 do 
        if Bst.remove bst keys1.(i) then removed := !removed @ [keys1.(i)]
      done) ;
    
    Atomic.final (fun () ->
      let items = Bst.to_list bst in 
      Atomic.check (fun () -> 
        let _ = List.iter (fun x -> Printf.printf "%d " x) items ; print_endline "" ; List.iter (fun x -> Printf.printf "%d " x) !removed in List.length items + List.length !removed = siz)
    )
  )

let remove_remove () = 
  Atomic.trace (fun () -> 
    let bst = Bst.create ~compare:Int.compare () in 
    let keys = [|50 ; 30 ; 70 ; 40 ; 20 ; 60 ; 80 ; 10|] in 
    let siz = 8 in 
    for i = 0 to siz - 1 do 
      Bst.add bst keys.(i)
    done ;
    let r1 = ref 0 in 
    let r2 = ref 0 in 

    Atomic.spawn(fun () -> 
      for i = 0 to 4 do 
        if Bst.remove bst keys.(i) then r1 := !r1 + 1
      done) ;
    Atomic.spawn(fun () ->
      for i = 3 to 7 do
        if Bst.remove bst keys.(i) then r2 := !r2 + 1
      done) ;

    Atomic.final(fun () ->
      let items = Bst.to_list bst in 
      Atomic.check (fun () -> List.length items = 0) ;
      Atomic.check (fun () -> !r1 + !r2 = 8) ;
    )
  )

let () = 
  let open Alcotest in 
  run "DSCheck_Bst"
    [
      ( "basic",
        [
          test_case "2-disjoint-insert" `Slow insert_insert ;
          test_case "2-insert-duplicates" `Slow insert_insert_duplicates ;
          test_case "1-insert-1-search" `Slow insert_search ;
          test_case "2-insert-balanced" `Slow insert_insert_balanced ;
          test_case "1-insert-1-search-balanced" `Slow insert_search_balanced ;
          test_case "1-insert-1-remove" `Slow insert_remove ;
          test_case "1-insert-1-remove-1-search-balanced" `Slow insert_remove_search_balanced ;
          test_case "1-remove-1-remove" `Slow remove_remove ; 
        ]
      ) ;
    ]