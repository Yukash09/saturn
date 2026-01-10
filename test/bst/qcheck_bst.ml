module Bst_ez = struct 
  include Saturn.Bst_ez
end
let tests_two_domains = 
  QCheck.
  [
    (* Two domains doing multiple adds *)
    Test.make ~name:"2-insert-disjoint-parallel" (pair nat_small nat_small)
      (fun (npush1 , npush2) -> 
        let bst = Bst_ez.create ~compare:Int.compare () in 
        let barrier = Barrier.create 2 in 
        let lpush1 = List.init npush1 (fun i -> i) in 
        let lpush2 = List.init npush2 (fun i -> i + npush1) in
        let work lpush = List.map (Bst_ez.add bst) lpush in 
        let domain1 = 
          Domain.spawn @@ fun () ->
          Barrier.await barrier ;
          work lpush1 in 
        let _popped2 = 
          Barrier.await barrier ;
          work lpush2 in
        
        let _popped1 = Domain.join domain1 in 
        let items = Bst_ez.to_list bst in 
        let _ = List.iter (fun (x) -> Printf.printf "(%d) " x) items in 
        let _ = Printf.printf "This test done: npush1 = %d , npush2 = %d \n%!" npush1 npush2 in 
        List.length items = (npush1 + npush2));
  ]




let () = 
  let to_alcotest = List.map QCheck_alcotest.to_alcotest in 
  Alcotest.run "QCheck Bst"
    [
      ("tests_two_domains" , to_alcotest tests_two_domains) ;
    ]