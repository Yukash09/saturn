type 'elt node = 
Null
| Node of {
    mutable mkey : bool * 'elt option;  (*None means inf, Some x means x*)
    mutable lchild : (bool * bool * bool * bool * 'elt node) Atomic.t;
    mutable rchild : (bool * bool * bool * bool * 'elt node) Atomic.t; 
    mutable replace : bool;
}

(* might need to de-atomicify node_m *)
(* and 'elt node = 'elt node_m Atomic.t *)

type edge_type = 
| Left 
| Right

type 'elt edge = 
| Null_edge
| Edge of {
  mutable parent : (bool * bool * bool * bool * 'elt node) Atomic.t;
  mutable child : (bool * bool * bool * bool * 'elt node) Atomic.t; 
  mutable which : edge_type ; 
}

type 'elt seek_record =  {
  mutable last_edge : 'elt edge ; 
  mutable plast_edge : 'elt edge ; 
  mutable inject_edge : 'elt edge ;
}

type 'elt anchor_record =  {
  mutable anchor_node : 'elt node ; 
  mutable anchor_key : 'elt option ; 
}

type modes = 
| Inactive
| Injection 
| Discover
| Cleanup

type optype =
| Noop 
| Simple
| Complex 

type 'elt state_record = {
  mutable target_edge : 'elt edge ; 
  mutable ptarget_edge : 'elt edge ; 
  mutable target_key : 'elt option ; 
  mutable curr_key : 'elt option ; 
  mutable mode : modes ;
  mutable wtype : optype ; 
  mutable succ_record : 'elt seek_record ; 
}

type 'elt t = {
  compare : 'elt -> 'elt -> int ;
  mutable root : 'elt node ; 
  my_state : 'elt state_record Domain.DLS.key
}

let print_mode mode = 
  match mode with
  | Inactive -> print_endline "Inactive"
  | Injection -> print_endline "Injection" 
  | Discover -> print_endline "Discover"
  | Cleanup -> print_endline "Cleanup" 

let print_op op = 
  match op with
  | Noop -> print_endline "Noop"
  | Simple -> print_endline "Simple"
  | Complex -> print_endline "Complex"

let print_node node _printfn = (*let's assume this thing doesn't require node to be atomic*)
  match node with
  | Null -> print_endline "Null node"
  | Node {mkey = (_, key);_} -> (
      match key with
      | None -> print_endline "inf"
      | Some x -> _printfn x ; print_endline ""
  ) 

let print_which which = 
  match which with
  | Left -> print_endline "Left"
  | Right -> print_endline "Right"

let print_edge edge _printfn = 
  match edge with
  | Null_edge -> print_endline "Null edge"
  | Edge {parent; child ; which} -> (
    let (_, _, _, _, p) = Atomic.get parent in
    let (_, _, _, _, c) = Atomic.get child in
    print_string "parent: "; print_node p _printfn; print_string "child: "; print_node c _printfn; print_string "type: "; print_which which
  )

let print_tuple tuple _printfn = 
match Atomic.get tuple with
| (n, i, d, p, node) -> (
  if n then print_string "true " else print_string "false "; 
  if i then print_string "true " else print_string "false ";
  if d then print_string "true " else print_string "false ";
  if p then print_string "true " else print_string "false ";
  print_node (Atomic.get node) _printfn;
)

let rec inorder_helper root = 
  match root with 
    | Null -> []
    | Node {mkey = (_, key); lchild; rchild; _} -> 
        let (l, _, _, _, left) = Atomic.get lchild in
        let (r, _, _, _, right) = Atomic.get rchild in
        let mlist = 
        (
          match key with
          | None -> (*print_endline "inf"; print_string "left: "; print_tuple lchild _printfn; print_string "right: "; print_tuple rchild _printfn;*) []
          | Some x -> (*_printfn x; print_endline ""; print_string "left: "; print_tuple lchild _printfn; print_string "right: "; print_tuple rchild _printfn;*) [x]
        ) in
        let llist = if l then [] else inorder_helper left in
        let rlist = if r then [] else inorder_helper right in
        llist @ mlist @ rlist

let _to_list tree _printfn = 
  match tree with {root;_} -> inorder_helper root

let print_inorder root _printfn = 
   let list = _to_list root _printfn in
   let rec printer list _printfn = 
     match list with
     | [] -> ()
     | x::xs -> _printfn x; Printf.printf " " ;printer xs _printfn
   in print_string "inorder: "; printer list _printfn; print_endline "" 

let create ~compare () = 
  let t_node = (Node {mkey = (false, None); lchild = Atomic.make (true, false, false, false, Null); rchild = Atomic.make (true, false, false, false, Null); replace = false}) in
  let s_node = (Node {mkey = (false, None); lchild = Atomic.make (true, false, false, false, Null); rchild = Atomic.make (false, false, false, false, t_node); replace = false}) in
  let state = Domain.DLS.new_key (fun () ->
      {
        target_key = None ;
        target_edge = Null_edge ;
        ptarget_edge = Null_edge ;
        curr_key = None ;
        mode = Inactive ;
        wtype = Noop ;
        succ_record = {
          last_edge = Null_edge ;
          plast_edge = Null_edge ;
          inject_edge = Null_edge ;
        }
      }
    ) in 
  {compare ; root = (Node {mkey = (false, None); lchild = Atomic.make (true, false, false, false, Null); rchild = Atomic.make (false, false, false, false, s_node); replace = false}) ; my_state = state}

let seek (key : 'elt) (srecord : 'elt seek_record ref) (tree : 'elt t)  = 
  begin
    (* ignore(print_endline "---------------- entered seek ----------------"); *)
    let cmp = tree.compare in 
    let _R = tree.root in (* Node R*)
    let _S = (*Node S *)
      begin match _R with 
      | Null -> Null (* Is this correct? *)
      | Node {mkey = _ ; lchild = _ ; rchild; replace = _} -> let (_ , _ , _ , _ , rnode) = Atomic.get rchild in rnode 
      end  
      in 
    let _T = (* Node T *)
      begin match _S with 
      | Null -> Null (* Is this correct sir? *)
      | Node {mkey = _; lchild = _ ; rchild; replace = _} -> let (_ , _ , _ , _ , rnode) = Atomic.get rchild in rnode  
      end 
      in 
    let p_anch_record : 'elt anchor_record ref = (* This should be in DLS ?*)
      ref {anchor_node = _S ; anchor_key = None} in 
    let p_seek : 'elt seek_record ref =  (* This should be in DLS ?*)
      ref ({last_edge = !srecord.last_edge ; plast_edge = !srecord.plast_edge ; inject_edge = !srecord.inject_edge }) in 

    let out_flag = ref true in (* Flag for outermost while loop *)
    while !out_flag do 
        let track_plast_edge : 'elt edge ref = (* This should be in DLS ?*) (* pLastEdge *)
          ref (Edge {parent = Atomic.make (false, false, false, false, _R) ; child = Atomic.make (false, false, false, false, _S) ; which = Right}) in 
        let track_last_edge : 'elt edge ref = (* This should be in DLS ?*) (* lastEdge *)
          ref (Edge {parent = Atomic.make (false, false, false, false, _S) ; child = Atomic.make (false, false, false, false, _T) ; which = Right}) in 
        let curr : (bool* bool* bool* bool *'elt node) Atomic.t ref = (* This should be in DLS ?*)
          ref (Atomic.make (false, false, false, false, _T)) in 
        let anch_record : 'elt anchor_record = (* This should be in DLS ? , nah this aint ref but it has ref? Idk mannn *) (* anchorRecord *)
          {anchor_node = _S ; anchor_key = None} in 
        let in_flag = ref true in (* Flag for innermost while loop *)
        while !in_flag do 
            (* Read the key stored in the current node *)
            let (_, _, _, _, curr_node) = Atomic.get !curr in
            let ckey = 
              begin match curr_node with 
              | Null -> raise (failwith "Gah! Null at ckey!")
              | Node {mkey = (_ , reqkey) ; lchild = _ ; rchild = _ ; replace = _} -> reqkey
              end in 

            (* Find the next edge using BST property *)
            let cmpval = (
                match ckey with
                | None -> -1 (*this means ckey is infinity*)
                | Some ckey -> cmp key ckey
            )
            in
            let which = if cmpval < 0 then (Left) else (Right) in 
            let next = 
              begin match which with 
                | Left -> begin match curr_node with 
                        | Null -> Atomic.make (false, false, false, false, Null)
                        | Node {mkey = _ ; lchild ; rchild = _ ; replace = _ } -> lchild 
                        end
                | Right -> begin match curr_node with 
                        | Null -> Atomic.make (false, false, false, false, Null)
                        | Node {mkey = _ ; lchild = _ ; rchild  ; replace = _ } -> rchild 
                        end
              end
            in 
            let (n, _, _, _, _) = Atomic.get next in

            if (cmpval = 0 || n) then 
              (* Key found or Null encountered *)
            begin
              !srecord.plast_edge <- !track_plast_edge ;
              !srecord.last_edge <- !track_last_edge ; 
              !srecord.inject_edge <- Edge {parent = !curr ; child = next ; which = which} ;
              if (cmpval = 0) then 
               (* Keys match, we should just return *)
               (* return *) 
               begin 
                 in_flag := false ; 
                 out_flag := false ; 
                 (* raise (failwith "Please return 1") (* god please help me*) Ok I have temporarily fixed with the outer flag, idk if it works though *)
               end 
              else (in_flag := false) (* break *)
            end
            else () ;

            if (!in_flag) && (!out_flag) then (* don't do if false? --> yes *)
              begin match which with 
              | Right -> anch_record.anchor_node <- curr_node ; anch_record.anchor_key <- ckey 
              | Left -> ()
              end ;

            if (!in_flag) && !out_flag then (*bcz it's a break!*)
            begin
              track_plast_edge := !track_last_edge ;
              track_last_edge := (Edge {parent = !curr ; child = next ; which = which}) ;
              curr := next 
            end
        done (* inner while loop donesh *) ;

        if (!out_flag) then
        begin
          let (_ , _ , d , p , _) = 
            begin match (anch_record.anchor_node) with 
            | Null -> raise (failwith "Wat the hail oooo ooo 2") (* Baccha I'm abusing this atp *)
            | Node {mkey = _ ; lchild = _ ; rchild ; replace = _} -> Atomic.get rchild 
            end in 
          if not (d) && not (p) then 
            let (_ , akey) = 
              begin match (anch_record.anchor_node) with 
              | Null -> raise (failwith "Wat the hail oooo ooo 3") (* No comments this time *)
              | Node {mkey ; lchild = _ ; rchild = _ ; replace = _} -> mkey 
              end in 

              if (anch_record.anchor_key = akey) then 
                begin
                  (* print_endline "should enter this"; *)
                  out_flag := false ; 
                  (* raise (failwith "Please return 2") ; (* return :( *)*)
                end ;
          else
            if (!p_anch_record.anchor_key = anch_record.anchor_key) && (!out_flag) then 
              begin srecord := !p_seek ; 
                  out_flag := false ; 
                  (* raise (failwith "Please return 3") ; (* return :( *)*)
              end ;
          if (!out_flag) then
            begin
              p_seek := !srecord ;
              p_anch_record := anch_record ;
            end
        end
    done;
    (* ignore(print_endline "---------------- exited seek ----------------"); *)
  end

(* let debug () *)
let _find (tree : 'elt t) (key : 'elt) (_printfn : 'elt -> unit) =
  begin
    let my_srecord = ref {last_edge = Null_edge; plast_edge = Null_edge; inject_edge = Null_edge} 
    in seek key my_srecord tree;
    let node =  match ((!my_srecord).last_edge) with
    | Null_edge -> Null
    | Edge{child;_} -> let (_, _, _, _, child) = Atomic.get child in child
    in 
    let nkey = 
      match node with
      | Null -> None
      | Node{mkey = (_, key_val);_} -> key_val
    in
    if (nkey = Some key) then true 
    else false
  end

let update_mode (tree: 'elt t) = 
begin
  (* print_endline "--------------entered um--------------"; *)
  match (Domain.DLS.get tree.my_state).wtype with 
  | Simple -> (Domain.DLS.get tree.my_state).mode <- Cleanup
  | Complex -> 
    let node = 
      begin match (Domain.DLS.get tree.my_state).target_edge with 
      | Null_edge -> raise (failwith "Null edge upd_mode1")
      | Edge {parent =_ ; child  ; which = _} -> let (_ , _ , _ , _ , childnode) = Atomic.get child  in childnode
      end in 
      begin match node with 
      | Null -> raise (failwith "Null node upd_mode2")
      | Node {mkey = _ ; lchild = _ ; rchild = _ ; replace} -> 
        if replace then (Domain.DLS.get tree.my_state).mode <- Cleanup else (Domain.DLS.get tree.my_state).mode <- Discover
      end
  | Noop -> ignore(raise (failwith "How did you end up here in update_mode?"))
  ;
  (* print_endline "--------------exited um--------------"; *)
end

let initialize_type_and_update_mode (tree:'elt t) = 
begin
  (* print_endline "============entered itaum============"; *)
  let node = 
    begin match (Domain.DLS.get tree.my_state).target_edge with 
    | Null_edge -> raise (failwith "Null edge upd_mode1")
    | Edge {parent = _ ; child ; which = _} -> let (_ , _ , _ , _ , childnode) = Atomic.get child in childnode
    end in 
  let (lN , _ , _ , _ , _) = 
    begin match node with 
    | Null -> raise (failwith "Null node itaum1") 
    | Node {mkey = _ ; lchild ; rchild = _ ; replace = _} -> Atomic.get lchild
    end in 
  let (rN , _ , _ , _ , _) = 
    begin match node with 
    | Null -> raise (failwith "Null node itaum1") 
    | Node {mkey = _ ; lchild = _ ; rchild  ; replace = _} -> Atomic.get rchild
    end in 
  if lN || rN then 
    begin 
      let (m , _) = 
      begin match node with 
      | Null -> raise (failwith "Null node itaum1") 
      | Node {mkey ; lchild = _ ; rchild = _  ; replace = _} -> mkey
      end in
      if m then (Domain.DLS.get tree.my_state).wtype <- Complex else (Domain.DLS.get tree.my_state).wtype <- Simple
    end
  else (Domain.DLS.get tree.my_state).wtype <- Complex ;
  update_mode tree;
  (* print_endline "============exited itaum============";  *)
end

let find_smallest (tree: 'elt t) (_printfn : 'elt -> unit) = 
 begin
  (* print_endline "============entered fs============"; *)
  (*find the node with the smallest key in the subtree rooted at the right child of the target node*)
  let inject_edge = ref Null_edge in
  let last_edge = ref Null_edge in
  let plast_edge = ref Null_edge in
  let node = (
    match (Domain.DLS.get tree.my_state).target_edge with
    | Null_edge -> raise (failwith "Null edge in findsmallest")
    | Edge {child;_} -> child
  ) in
  let srecord = (Domain.DLS.get tree.my_state).succ_record in
  let right = (
    let (_, _, _, _, node) = Atomic.get node in
    match node with 
    | Null -> raise (failwith "Null node in failwith")
    | Node {rchild;_} -> rchild
  ) in
  let retval = ref false in 
  let (n, _, _, _, _) = Atomic.get right in
  if n then (
    retval := false;
  )
  else ( (*writing else here in place of return in if*)
    last_edge := Edge {parent = node; child = right; which = Right};
    plast_edge := Edge {parent = node; child = right; which = Right};
    let out_flag = ref true in
    while !out_flag do
      let curr = (
        match !last_edge with
        | Null_edge -> raise (failwith "Shouldn't reach here")
        | Edge {child;_} -> child
      ) in
      let left = (
        let (_, _, _, _, child) = Atomic.get curr in
        match child with
        | Null -> raise (failwith "Another null in find smalles")
        | Node {lchild; _} -> lchild
      ) in
      let (n, _, _, _, _) = Atomic.get left in
      if n then (
        (*reacged the node with the smallest key*)
        inject_edge := Edge {parent = curr; child = left; which = Left};
        out_flag := false (*break*)
      );
      if !out_flag then (
        (*traverse the next edge*)
        plast_edge := !last_edge;
        last_edge := Edge {parent = curr; child = left; which = Left};
      )
    done;
    srecord.last_edge <- !last_edge;
    srecord.plast_edge <- !plast_edge;
    srecord.inject_edge <- !inject_edge;
    retval := true;
  );
  (* print_endline "============exited fs============"; *)
  !retval
 end

let rec _add (tree: 'elt t) (key:'elt) (_printfn: 'elt -> unit) = 
   let out_flag = ref true in 
  let retval = ref false in
  let target_record : 'elt seek_record ref = ref {last_edge = Null_edge ; plast_edge = Null_edge ; inject_edge = Null_edge} in 
  while !out_flag do
    seek key target_record tree; 
    let target_edge = !target_record.last_edge in 
    let tnode_tuple = begin match target_edge with 
                | Null_edge -> raise (failwith "Null Edge 1")
                | Edge {parent = _ ; child ; which = _} -> Atomic.get child 
                end in
    let (_, _, _, _, tnode) = tnode_tuple in
    let nkey = begin match tnode with
                  | Null -> raise (failwith "Null Node 1")
                  | Node {mkey = (_ , skey) ; lchild = _ ; rchild = _ ; replace = _} -> skey
                  end in
    let cmpval = (
      match nkey with
      | None -> -1
      | Some nkey -> tree.compare key nkey
    ) 
    in 
    if cmpval = 0 then 
      begin 
        retval := false ; 
        out_flag := false ;
      end
    else 
      let newnode = (Node {mkey = (false , Some key) ; lchild = Atomic.make (true, false, false, false, Null) ; rchild = Atomic.make (true, false, false, false, Null) ; replace = false}) in 
      let (address ,which) = begin match !target_record.inject_edge with 
                  | Null_edge -> raise (failwith "Null Edge 2")
                  | Edge {parent = _ ; child ; which} -> (Atomic.get child ,which)
                  end in 
      let before = begin match tnode with 
                  | Null -> raise (failwith "Null Node 2")
                  | Node {mkey = _ ; lchild ; rchild ; replace = _} -> match which with 
                  | Left -> lchild 
                  | Right -> rchild 
                  end in
      let result = Atomic.compare_and_set before address (false , false , false , false , newnode) in (* Does this even work? Idk I shall become theist *)
      if result then (out_flag := false ; retval := true);
      let (_, _, d, p, _) = (
        match tnode with
        | Null -> raise (failwith "yet another null node")
        | Node {lchild; rchild; _} -> (
          match which with
          | Left -> Atomic.get lchild
          | Right -> Atomic.get rchild
        )
      ) in
      if d then help_target_node tree target_edge _printfn
      else if p then help_successor_node tree target_edge _printfn 
      (* Currently we are not in the mood to help other domains *)
  done ; !retval 

  and find_and_mark_successor (tree : 'elt t) (_printfn : 'elt -> unit) = 
  begin
    (* print_endline "************entered fams************"; *)
    let node = (
      match (Domain.DLS.get tree.my_state).target_edge with
      | Null_edge -> raise (failwith "Why da edge null?")
      | Edge {child;_} -> Atomic.get child
    ) in 
    let srecord = (Domain.DLS.get tree.my_state).succ_record in
    let out_flag = ref true in
    while !out_flag do
      (*read the mark flag of the target node*)
      let (m, _) = (
        let (_, _, _, _, cnode) = node in
        match cnode with
        | Null -> raise (failwith "Null node, why?")
        | Node {mkey;_} -> mkey
      ) in 
      (*find the node with the smallest key in the right subtree*)
      let result = find_smallest tree _printfn in
      if (m || (not result)) then (
        (*successor node had already been selected before the traversal or the right subtree is empty*)
        (*not changing the flag here bcz the else does the same thing in this case*)
      )
      else (
        (*retrieve the info from the seek record*)
        let succ_edge = srecord.last_edge in
        let left = (
          match srecord.inject_edge with
          | Null_edge -> raise (failwith "Null edges. Null edges everywhere!")
          | Edge {child;_} -> Atomic.get child
        ) in
        (*read the mark flag of the key under deletion*)
        let (m, _) = (
        let (_, _, _, _, cnode) = node in
          match cnode with
          | Null -> raise (failwith "Ayyo, another Null node. Why?")
          | Node {mkey;_} -> mkey
        ) in 
        (*
          original line was to continue if m... so I'm doing if not m
        *)
        if not m then (
          (*try to set the promote flag on the left edge*)
          let casnode = (
            let succ_child = (
              match succ_edge with
              | Null_edge -> raise (failwith "Null succ edge")
              | Edge {child;_} -> child
            ) in
            (
              let (_, _, _, _, lchild) = Atomic.get succ_child in
              match lchild with
              | Null -> raise (failwith "Null nodeeee")
              | Node {lchild;_} -> lchild
            )
          ) in
          let newnode = (
            match node with (_, _, _, _, node) -> (true, false, false, true, node)
          ) in
          let result = Atomic.compare_and_set casnode left newnode in
          if result then out_flag := false
          else (
            (*attempt to mark the edge failed; recover from the failure and retry if needed*)
            let (n, _, d, _, _) = (
              match succ_edge with 
              | Null_edge -> raise (failwith "Nullll")
              | Edge {child;_} -> (
                match Atomic.get child with
                | (_, _, _, _, cnode) -> (
                  match cnode with
                  | Null -> raise (failwith "Nulllnode")
                  | Node {lchild;_} -> Atomic.get lchild
                )
              )
            )
            in
            if (n && d) then help_target_node tree succ_edge _printfn;
          )
        )
      ) 
    done;
    update_mode tree ;
    (* print_endline "************exited fams************"; *)
  end

and mark_child_edge (tree : 'elt t) (which : edge_type) (_printfn : 'elt -> unit) = 
  begin
    (* print_endline "========begin marking child edge========"; *)
    let edge = ref Null_edge in
    let flag = ref 0 in (*1 is delete and 2 is promote*)
    (* print_mode (state.mode); *)
    if (Domain.DLS.get tree.my_state).mode = Injection then (
      edge := (Domain.DLS.get tree.my_state).target_edge;
      flag := 1
    )
    else (
      edge := (Domain.DLS.get tree.my_state).succ_record.last_edge;
      flag := 2
    );
    (* print_edge (!edge) _printfn; *)
    let node = (
      match !edge with
      | Null_edge -> raise (failwith "Too many null edge exceptions")
      | Edge {child;_} -> child
    ) in
    let out_flag = ref true in
    let retval = ref false in
    while !out_flag do
      let addr = (
        let (_, _, _, _, node) = Atomic.get node in 
        match node with
        | Null -> raise (failwith "mark child edge null node")
        | Node {lchild; rchild; _} -> (
          match which with 
          | Left -> lchild
          | Right -> rchild
        )
      ) in 
      let (_, i, d, p, _) = Atomic.get addr in
      (* print_tuple addr _printfn; *)
      if i then (
        help_target_node tree (Edge {parent = node; child = addr; which = which}) _printfn;
        out_flag := false
      )
      else if d then (
        if !flag = 1 then (
          help_target_node tree !edge _printfn;
          retval := false
        )
        else (
          retval := true
        );
        out_flag := false
      )
      else if p then (
        if !flag = 2 then (
          help_successor_node tree !edge _printfn;
          retval := false
        )
        else (
          retval := true
        );
        out_flag := false
      )
      else ();
      if !out_flag then (
        (*you'll only reach here if non-null flags are off, so peace: This is in context of the given pseudocode*)
        let oldnode = (
          let (_, _, _, _, node) = Atomic.get node in 
          match node with
          | Null -> raise (failwith "mark child edge null node")
          | Node {lchild; rchild; _} -> (
            match which with 
            | Left -> Atomic.get lchild
            | Right -> Atomic.get rchild
          )
        ) in
       let newnode = (
          match oldnode with
          | (n, _, _, _, onode) -> (
            match !flag with
            | 1 -> (n, false, true, false, onode)
            | 2 -> (n, false, false, true, onode)
            | _ -> raise (failwith "ur not supposed to reach here")
          )
       ) in
       let currnode = (
          let (_, _, _, _, node) = Atomic.get node in 
          match node with
          | Null -> raise (failwith "mark child edge null node")
          | Node {lchild; rchild; _} -> (
            match which with 
            | Left -> lchild
            | Right -> rchild
          )
       ) in
       
       retval := Atomic.compare_and_set currnode oldnode newnode;
       if (!retval) then out_flag := false;
      )
    done;
    (* print_endline "========end marking child edge========"; *)
    !retval
  end

and inject (tree : 'elt t) (_printfn : 'elt -> unit) = 
  begin
    (* print_endline "<><><><><> entered inject <><><><><>"; *)
    let target_edge = (Domain.DLS.get tree.my_state).target_edge in
    (* print_edge target_edge _printfn; *)
    let ((_, _, _, _, parent), child, which) = (
      match target_edge with
      | Null_edge -> raise (failwith "Tell me again, why is the target edge null?")
      | Edge {parent;child;which} -> (Atomic.get parent, child, which)
    ) in
    let curr_node = (
      match parent with
      | Null -> raise (failwith "Null parent")
      | Node {lchild;rchild;_} -> (
        match which with 
        | Left -> lchild
        | Right -> rchild
      ) 
    ) in
    let new_node = (
      match (Atomic.get child) with (_, _, _, _, cnode) -> (false, true, false, false, cnode)
    ) in
    (* print_string "before CAS: ";print_tuple curr_node _printfn; *)
    let result = Atomic.compare_and_set curr_node (Atomic.get child) new_node in
    (* print_string "maybe I'm wrong: "; print_tuple child _printfn;
    print_string "after CAS: ";print_tuple curr_node _printfn; *)
    if not result then (
      (*unable to set the intent flag; help if needed*)
      let (_, i, d, p, _) = (
        match parent with
        | Null -> raise (failwith "Null parent 2")
        | Node {lchild;rchild;_} -> (
          match which with 
          | Left -> Atomic.get lchild
          | Right -> Atomic.get rchild
        ) 
      ) in
      if i then help_target_node tree target_edge _printfn
      else if d then help_target_node tree ((Domain.DLS.get tree.my_state).ptarget_edge) _printfn
      else if p then help_successor_node tree ((Domain.DLS.get tree.my_state).ptarget_edge) _printfn
    ) else (
      (*mark left edge for deletion*)
      let result = mark_child_edge tree Left _printfn in
      if not result then ()
      else (
        (*mark the right edge for deletion; cannot fail*)
        ignore(mark_child_edge tree Right _printfn);
        initialize_type_and_update_mode tree
      )
    );
    (* print_endline "<><><><><> exited inject <><><><><>"; *)
  end 

and remove_successor (tree : 'elt t) (_printfn : 'elt -> unit)= 
begin
  (* print_endline "+++++++++++++entered remsuc+++++++++++++"; *)
  let retflag = ref false in 
  let node1 =
    begin 
      match (Domain.DLS.get tree.my_state).target_edge with 
      | Null_edge -> raise (failwith "Null edge rms1")
      | Edge {parent = _ ; child ; which = _ } -> let (_ , _ , _ , _ , childnode) = Atomic.get child in ref childnode
    end in 
    let seekrec = (Domain.DLS.get tree.my_state).succ_record in 
    let succ_edge = ref seekrec.last_edge in 
    let (_ , _ , _ , p , address) = 
      begin match !succ_edge with 
      | Null_edge -> raise (failwith "Null edge rms2")
      | Edge {parent = _ ; child  ; which = _} -> let  (_ , _ , _ , _ , childnode) = Atomic.get child in
        begin match childnode with 
        | Null -> raise (failwith "Null Node child rms3")
        | Node {mkey = _ ; lchild ; rchild = _ ; replace = _} -> Atomic.get lchild
        end
      end in
    (*!!!!!!!!!!!!!!!!!!!!!!!!!!!THIS IS NOT PERMANENT I REPLACED <> WITH NOT ==!!!!!!!!!!!!!!!!!!!!!!!!!*)
    if not (p) || not (address == !node1) then 
      begin
        begin match !node1 with 
        | Null -> raise (failwith "Null node rms4")
        | Node {mkey  ; lchild ; rchild  ; replace = _} -> ignore(node1 := (Node {mkey ; lchild ; rchild ; replace = true}))
        end ;
        update_mode tree ;
        retflag := true 
      end ;
    if !retflag then () 
    else 
      begin 
        ignore(mark_child_edge tree Right _printfn) ; 
        begin match !node1 with 
        | Null -> raise (failwith "Null node rms4")
        | Node {mkey = _  ; lchild ; rchild  ; replace = _} -> 
          begin match !succ_edge with 
          | Null_edge -> raise (failwith "Null edge rm5")
          | Edge {parent = _ ; child  ; which = _} -> let (_ , _ , _ , _ , childnode) = Atomic.get child in 
            begin match childnode with 
            | Null -> raise (failwith "Null node rms6")
            | Node {mkey = (_ , mkey) ; lchild = _ ; rchild = _ ; replace = _} -> 
              (* (node1 := Atomic.make (Node {mkey = (true , mkey) ; lchild ; rchild ; replace = true})); *)
              ignore(node1 := (Node {mkey = (true , mkey) ; lchild ; rchild ; replace = true}))
            end;
          end 
        end ;
        let out_flag = ref true in 
        while !out_flag do 
          let succ_edge_parent = 
            begin match !succ_edge with 
            | Null_edge -> raise (failwith "Null edge rms7")
            | Edge {parent ; child = _ ; which = _} -> let (_ , _ , _ , _ , parent_node) = Atomic.get parent in parent_node
            end in
          let dflag = 
          if succ_edge_parent == !node1 then true else false in 
          let which = 
          if succ_edge_parent == !node1 then Right else Left in 
          (*!!!!!!!!! I DIDN'T USE THE i SHOULD SEE !!!!!!!!!!*)
          let (_ , _i , _ , _ , _) = 
            begin match succ_edge_parent with 
            | Null -> raise (failwith "Null node rms8")
            | Node {mkey = _ ; lchild ; rchild ; replace = _} -> 
              begin match which with 
              | Left -> Atomic.get lchild
              | Right -> Atomic.get rchild 
              end
            end in 
          (* let succ_edge_child = 
            begin match !succ_edge with 
            | Null_edge -> raise (failwith "Null edge rms9")
            | Edge {parent = _ ; child ; which = _ } -> let (_ , _ , _ , _ , childnode) = Atomic.get child in childnode
            end in 
          let (n , _ , _ , _ , right) = 
            begin match Atomic.get succ_edge_child with 
            | Null -> raise (failwith "Null node rms10")
            | Node {mkey = _ ; lchild = _ ; rchild ; replace = _} -> Atomic.get rchild
            end in
          let oldvalue = (false , i , dflag , false , succ_edge_child) in  *)
           let succ_edge_child = 
            begin match !succ_edge with 
            | Null_edge -> raise (failwith "Null edge rms9")
            | Edge {parent = _ ; child ; which = _ } -> child
            end in 
          let (n , _ , _ , _ , right) = 
            let (_, _, _, _, childnode) = Atomic.get succ_edge_child in
            begin match childnode with 
            | Null -> raise (failwith "Null node rms10")
            | Node {mkey = _ ; lchild = _ ; rchild ; replace = _} -> Atomic.get rchild
            end in
          let oldvalue = Atomic.get succ_edge_child in 
          let (_, _, _, _, suc_ed_child) = Atomic.get succ_edge_child in
          let newvalue = 
            if n then (true , false , dflag , false , suc_ed_child) else (false , false , dflag , false , right) in 

          let before = 
            begin match succ_edge_parent with 
            | Null -> raise (failwith "Null node rms11")
            | Node {mkey = _ ; lchild ; rchild ; replace = _} ->
              begin match which with 
              | Left -> lchild 
              | Right -> rchild 
              end 
            end in 
          let result = ref (Atomic.compare_and_set before oldvalue newvalue) in
          
          if !result || dflag then out_flag := false ;

          if !out_flag then 
          begin 
            let (_ , _ , d , _ , _) = 
              begin match succ_edge_parent with 
              | Null -> raise (failwith "Null node rms11")
              | Node {mkey = _ ; lchild ; rchild ; replace = _} ->
                begin match which with 
                | Left -> Atomic.get lchild 
                | Right -> Atomic.get rchild 
              end 
            end in 
            let plast_edge = seekrec.plast_edge in 
            let is_not_null = 
              begin match plast_edge with 
              | Null_edge -> false 
              | _ -> true
              end in 
            if d && (is_not_null) then 
              (* We are not helping *)
              help_target_node tree plast_edge _printfn;

            result := find_smallest tree _printfn; 
            let last_edge = seekrec.last_edge in 
            let last_edge_child = 
              begin match last_edge with 
              | Null_edge -> raise (failwith "Null edge rms12")
              | Edge {parent = _ ; child  ; which = _} -> let (_ , _ , _ , _ , childnode)  = Atomic.get child in childnode
              end in 
            (*ANOTHER CHANGE HERE, CHANGED = to == without any basis*)
            if not (!result) || (last_edge_child == suc_ed_child) 
              then (out_flag := false)
            else (succ_edge := seekrec.last_edge ;)
          end
          else ()
        done ;
        begin match !node1 with 
          | Null -> raise(failwith "Null node rms13")
          | Node {mkey ; lchild ; rchild ; replace = _} -> ignore(node1 := (Node {mkey ; lchild ; rchild ; replace = true}))
        end ;
        update_mode tree ;
      end;
      (* print_endline "+++++++++++++exited remsuc+++++++++++++"; *)
end

and cleanup (tree : 'elt t) (_printfn : 'elt -> unit) = 
  begin
    (* print_endline "<<<<<< cleanup begin >>>>>>"; *)
    let retval = ref false in
    let (parent, node, pWhich) = (
      match (Domain.DLS.get tree.my_state).target_edge with 
      | Null_edge -> raise (failwith "Null_edge")
      | Edge {parent;child;which} -> (
        let (_, _, _, _, parent) = Atomic.get parent in
        let (_, _, _, _, child) = Atomic.get child in
        (parent, child, which)
      )
    ) in
    
    if (Domain.DLS.get tree.my_state).wtype = Complex then (
      (*replace the node with a new copy in which all fields are unmarked*)
      let (_, nkey) = (
        match node with
        | Null -> raise (failwith "Null node in cleanup")
        | Node {mkey;_} -> mkey 
      ) in
      let newnode = Node {mkey = (false, nkey); lchild = Atomic.make (false, false, false, false, Null); rchild  = Atomic.make (false, false, false, false, Null); replace = false} in
      (*initialize left and right pointers*)
      let (_, _, _, _, left) = (
        match node with 
        | Null -> raise (failwith "Null node in cleanup 2")
        | Node {lchild;_} -> Atomic.get lchild
      ) in
      let newnode = (
        match newnode with
        | Null -> raise (failwith "Won't reach here")
        | Node r -> Node {r with lchild = Atomic.make (false, false, false, false, left)}
      ) in
      let (n, _, _, _, right) = (
        match node with
        | Null -> raise (failwith "Null node in cleanup 3")
        | Node {rchild;_} -> Atomic.get rchild
      ) in
      let rnode = (
        if n then (true, false, false, false, Null)
        else (false, false, false, false, right)
      ) in
      let newnode = (
        match newnode with
        | Null -> raise (failwith "Won't reach here")
        | Node r -> (false, false, false, false, (Node {r with rchild = Atomic.make rnode}))
      ) in
      (* (
        let (_, _, _, _, newnode) = newnode in
        print_node (Atomic.get newnode) _printfn;
        match Atomic.get newnode with
        | Null -> print_endline "baka!"
        | Node {lchild;rchild;_} ->
        print_string "lchild: "; print_tuple lchild _printfn;
        print_string "rchild: ";print_tuple rchild _printfn;
      ); *)
      let oldnode = (
        match (Domain.DLS.get tree.my_state).target_edge with
        | Null_edge -> raise (failwith "Null_edge 2")
        | Edge {child;_} -> Atomic.get child (*original algo needed old value to be node, and node comes from this, so yeah*) 
      ) in
      let currnode = (
        match parent with
        | Null -> raise (failwith "Null parent, gah!")
        | Node {lchild;rchild;_} -> (
          match pWhich with
          | Left -> lchild
          | Right -> rchild
        )
      ) in
      retval := Atomic.compare_and_set currnode oldnode newnode;
    )  
    else (
      (*remove the node*)
      (*determine to which grandchild will the edge at the parent be switched*)
      let (n, _, _, _, _) = (
        match node with 
        | Null -> raise (failwith "Null hi Null hy")
        | Node {lchild;_} -> Atomic.get lchild
      ) in
      let nWhich = if n then Right else Left in
      (*initialized the arguments of CAS*)
      let oldnode = (
        match (Domain.DLS.get tree.my_state).target_edge with
        | Null_edge -> raise (failwith "Null_edge 2")
        | Edge {child;_} -> Atomic.get child (*original algo needed old value to be node, and node comes from this, so yeah*) 
      ) in
      let (n, _, _, _, address) = (
         match node with 
        | Null -> raise (failwith "Null hi Null hy")
        | Node {lchild; rchild;_} -> (
          match nWhich with
          | Left -> Atomic.get lchild
          | Right -> Atomic.get rchild
        )
      ) in
      let newnode = (
        if n then (
          match (Domain.DLS.get tree.my_state).target_edge with
          | Null_edge -> raise (failwith "Null_edge 2")
          | Edge {child;_} -> (
            match (Atomic.get child) with
            | (_, _, _, _, cnode) -> (true, false, false, false, cnode)
          )
        )
        else (
          match (Domain.DLS.get tree.my_state).target_edge with
          | Null_edge -> raise (failwith "Null_edge 2")
          | Edge {child;_} -> (
            match (Atomic.get child) with
            | (_, _, _, _, _) -> (false, false, false, false, address)
          )
        ) 
      ) in
      let currnode = (
        match parent with
        | Null -> raise (failwith "Null parent, gah!")
        | Node {lchild;rchild;_} -> (
          match pWhich with
          | Left -> lchild
          | Right -> rchild
        )
      ) in
      
      retval := Atomic.compare_and_set currnode oldnode newnode;
    );
    (* print_endline "<<<<<<< cleanup end >>>>>>>"; *)
    !retval
  end

and help_target_node (tree : 'elt t) (help_edge : 'elt edge) (_printfn : 'elt -> unit) = 
begin
  (Domain.DLS.get tree.my_state).target_edge <- help_edge ;
  (Domain.DLS.get tree.my_state).mode <- Injection ; 
  let result = mark_child_edge tree Left _printfn in 
  let retflag = ref false in 
  if not result then retflag := true ; 
  if !retflag then () 
  else 
    begin 
      ignore(mark_child_edge tree Right _printfn) ; 
      initialize_type_and_update_mode tree ;
      if (Domain.DLS.get tree.my_state).mode = Discover then 
        find_and_mark_successor tree _printfn; 
      if (Domain.DLS.get tree.my_state).mode = Discover then 
        remove_successor tree _printfn;
      if (Domain.DLS.get tree.my_state).mode = Cleanup then 
        ignore(cleanup tree _printfn) ;
    end 
end

and help_successor_node (tree : 'elt t) (help_edge : 'elt edge) (_printfn : 'elt -> unit) = 
 begin 
  let parent, node = 
    begin match help_edge with 
      | Null_edge -> raise (failwith "Helper edge is Null, function -> help successor")
      | Edge {
        parent; 
        child; _
        } -> parent , child 
    end in 
  let left = 
    let (_, _, _, _, node) = Atomic.get node in
    begin match node with 
      | Null -> raise (failwith "Helper edge child node is Null, function -> help successor")
      | Node {lchild ; _} -> lchild 
    end in 
  (Domain.DLS.get tree.my_state).target_edge <- Edge {
    parent = Atomic.make (false, false, false, false, Null);
    child = left ;
    which = Right ; (* It doesn't matter I guess ?*)
  } ; 
  (Domain.DLS.get tree.my_state).succ_record.last_edge <- help_edge ;
  (Domain.DLS.get tree.my_state).succ_record.plast_edge <- Edge {
    parent = Atomic.make (false, false, false, false, Null);
    child = parent ;
    which = Right ; (* Again it doesn't matter? *)
  } ;
  remove_successor tree _printfn;
end
 
let _remove (tree : 'elt t) (key : 'elt) (_printfn : 'elt -> unit)= 
  begin
    (* print_endline "============entered remove============"; *)
    (Domain.DLS.get tree.my_state).target_key <- Some key ; 
    (Domain.DLS.get tree.my_state).curr_key <- Some key ;
    (Domain.DLS.get tree.my_state).mode <- Injection ;
    (* let my_state = {
      target_key = Some key;
      curr_key = Some key;
      mode = Injection;
      target_edge = Null_edge;
      ptarget_edge = Null_edge;
      wtype = Noop;
      succ_record = {last_edge = Null_edge; plast_edge = Null_edge; inject_edge = Null_edge}
    } in *)
    
    let out_flag = ref true in 
    let retval = ref false in
    let target_record : 'elt seek_record ref = ref {last_edge = Null_edge ; plast_edge = Null_edge ; inject_edge = Null_edge} in 
    while !out_flag do
      seek key target_record tree;
      let target_edge = !target_record.last_edge in
      let ptarget_edge = !target_record.plast_edge in
      let tnode_tuple = begin match target_edge with 
                | Null_edge -> raise (failwith "Null Edge 1")
                | Edge {parent = _ ; child ; which = _} -> child 
                end in
      let (_, _, _, _, tnode) = Atomic.get tnode_tuple in
      let nkey = begin match tnode with
                    | Null -> raise (failwith "Null Node 1")
                    | Node {mkey = (_ , skey) ; lchild = _ ; rchild = _ ; replace = _} -> skey
                    end in
      if not ((Domain.DLS.get tree.my_state).curr_key = nkey) then (
        (*key node doesn't exist in the tree*)
        (if ((Domain.DLS.get tree.my_state).mode = Injection) then retval := false else retval := true);
        out_flag := false; (*forcing a break out of the while loop*)
      );
      if !out_flag then (
        if ((Domain.DLS.get tree.my_state).mode = Injection) then (
          (Domain.DLS.get tree.my_state).target_edge <- target_edge; (*store reference to target edge*)
          (Domain.DLS.get tree.my_state).ptarget_edge <- ptarget_edge;
          inject tree _printfn; (*attempt to inject the operation at the node*)
        );
        (*mode would've changed if inject was successful*)
        if not ((Domain.DLS.get tree.my_state).mode = Injection) then (
          (*check if the target node found by the seek function matches the one stored in the state record*)
          let check = (
            match ((Domain.DLS.get tree.my_state).target_edge, target_edge) with
            | (Null_edge, Null_edge) -> false
            | (Null_edge, _) -> true
            | (_, Null_edge) -> true
            | (Edge {child = c1;_}, Edge {child = c2;_}) -> (
              let (_, _, _, _, c1)  = Atomic.get c1 in 
              let (_, _, _, _, c2)  = Atomic.get c2 in 
              not (c1 == c2) (*changed to physical here*)
            )
          ) in
          if (check) then (out_flag := false; retval := true; (*print_endline "return 2"*)); (*another return*)
          (*update the target edge infomation using the most recent seek*)
          if !out_flag then (Domain.DLS.get tree.my_state).target_edge <- target_edge; 

        );
        if !out_flag then (
          if ((Domain.DLS.get tree.my_state).mode = Discover) then (
            (*complex delete operation; locate the successor node and mark its child edges with promote flag*)
            find_and_mark_successor tree _printfn;
          );
          if ((Domain.DLS.get tree.my_state).mode = Discover) then (
            (*complex delete operation; promote the successor node's key and remove the successor node*)
            remove_successor tree _printfn;
          );
                    
          if ((Domain.DLS.get tree.my_state).mode = Cleanup) then (
            (*either remove the target node (simple delete) or replace it with a node with all fields unmarked (complex delete)*)
            let result = cleanup tree _printfn in
            if (result) then (out_flag := false; retval := true ;)
            else (
              let key = (
                match target_edge with
                | Null_edge -> raise (failwith "target edge is null Idk")
                | Edge {child;_} -> (
                  let  (_, _, _, _, cnode) = Atomic.get child in
                  match cnode with
                  | Null -> raise (failwith "key is null Idk")
                  | Node {mkey = (_, key);_} -> key 
                )
              ) in 
              (Domain.DLS.get tree.my_state).curr_key <- key 
            )
          );
        );
      )
    done; 
    (* print_endline "============exited remove============"; *)
    !retval
  end

let add tree elt = ignore(_add tree elt (fun _ -> ()))

let remove tree elt = _remove tree elt (fun _ -> ())

let find tree elt = _find tree elt (fun _ -> ())

let to_list tree = _to_list tree (fun _ -> ())