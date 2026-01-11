module Bst_ez = struct 
  include Saturn.Bst_ez
end

let seqtest () = 
  let bst = Bst_ez.create ~compare:Int.compare () in 
  Bst_ez.add bst 3 ;
  Bst_ez.add bst 4 ;
  ignore(Bst_ez.remove bst 3) ;
  ignore(Bst_ez.remove bst 4)
let test () = 
let bst = Bst_ez.create ~compare:Int.compare () in 
let barrier = Barrier.create 2 in 
let lpush1 = [5 ; 7 ; 3 ; 2 ; 4] in 
let lpush2 = [6 ; 8 ; 1 ; 0 ; 9] in 
let work lpush = List.iter (fun x -> Bst_ez.add bst x) lpush in 
let domain1 = 
  Domain.spawn @@ fun () -> 
  Barrier.await barrier ;
  work lpush1 in 

let _ =
  Barrier.await barrier ;
  work lpush2 in 

let _ = Domain.join domain1 in 
let items = Bst_ez.to_list bst in 
let _ = List.iter (fun (x) -> Printf.printf "(%d) " x) items in ()

let _ = seqtest () ;