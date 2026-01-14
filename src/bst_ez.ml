(* module Atomic = Multicore_magic.Transparent_atomic

type 'elt child = {
  flag : bool ;
  tag : bool ;
  address : 'elt node option ;
}

and 'elt node = {
  mutable key : 'elt option ; (* Option is being used to differentiate finite value keys and infinite keys for implementation purposes *)
  lchild : 'elt child Atomic.t ;
  rchild : 'elt child Atomic.t ;
}

type 'elt seek_record = {
  mutable ancestor : 'elt node  ;
  mutable successor : 'elt node  ;
  mutable parent : 'elt node  ;
  mutable leaf : 'elt node ;
}

type 'elt t = {
  compare : 'elt -> 'elt -> int ; (* Comparator *)
  root : 'elt node ; (* points to nodeR *)
  nodeS : 'elt node ; (* points to nodeS *)
}

let create ~compare () = 
begin 
  (* Create sentinel nodes - nodeR , nodeS , leaf1 , leaf2 for convenience *)

  let leaf1 = {
    key = None ;
    lchild = Atomic.make {
      flag = false ;
      tag = false ;
      address = None ; (* None represents Null node *)
    } ;
    rchild = Atomic.make {
      flag = false ;
      tag = false ;
      address = None ; (* None represents Null node *)
    } ;
  } in 

  let leaf2 = {
    key = None ; 
    lchild = Atomic.make {
      flag = false ;
      tag = false ;
      address = None ; (* None represents Null node *)
    } ;
    rchild = Atomic.make {
      flag = false ;
      tag = false ;
      address = None ; (* None represents Null node *)
    } ;
  } in 
  let leaf3 = {
    key = None ; 
    lchild = Atomic.make {
      flag = false ;
      tag = false ;
      address = None ; (* None represents Null node *)
    } ;
    rchild = Atomic.make {
      flag = false ;
      tag = false ;
      address = None ; (* None represents Null node *)
    } ;
  } in 

  let nodeS = {
    key = None ; 
    lchild = Atomic.make {
      flag = false ;
      tag = false ;
      address = Some (leaf1) ;
    } ;
    rchild = Atomic.make {
      flag = false ;
      tag = false ;
      address = Some (leaf2) ;
    } ;
  } in 

  let nodeR = {
    key = None ; 
    lchild = Atomic.make {
      flag = false ;
      tag = false ;
      address = Some (nodeS) ;
    } ;
    rchild = Atomic.make {
      flag = false ;
      tag = false ;
      address = Some (leaf3) ; (* None represents Null node *)
    } ;
  } in 
  let tree = {
    compare = compare ;
    root = nodeR ;
    nodeS = nodeS ;
  } in tree 
end
let seek (key : 'elt) (tree : 'elt t) = 
begin
  (* Initialize seek record using the sentinel nodes *)
  (* (Domain.DLS.get tree.srecord).ancestor <- tree.root ;
  (Domain.DLS.get tree.srecord).successor <- tree.nodeS ;
  (Domain.DLS.get tree.srecord).parent <- tree.nodeS ;   *)
  (* let _ = match (Atomic.get (tree.nodeS).lchild).address  with 
  | None -> print_endline "Not okie dokie start" ; raise Exit 
  | Some v -> print_endline "Start is okie dokie" in *)

  let srecord = {
    ancestor = tree.root ;
    successor = tree.nodeS ;
    parent = tree.nodeS ;
    leaf = Option.get (Atomic.get (tree.nodeS).lchild).address 
  } in 

  (* let left = Atomic.get !(tree.nodeS).lchild in 
  (Domain.DLS.get tree.srecord).leaf <- Option.get left.address ; *)

  (* Initialize other variables used in the traversal*)
  let parent_field = ref (Atomic.get ((srecord).parent).lchild) in 
  let curr_field = ref (Atomic.get ((srecord).leaf).lchild) in 
  let curr = ref !curr_field.address in 
  while !curr <> None do 
    (* Move down the tree, check if the edge from the (current) parent node in the access path is tagged *)

    if not !parent_field.tag then       
      (* Found an untagged edge in the access path, advance ancestor and successor pointers *)
    begin
      (srecord).ancestor <- (srecord).parent ;
      (srecord).successor <- (srecord).leaf ;
    end ;

    (* Advance parent and leaf pointers *)
    (srecord).parent <- (srecord).leaf ;
    (* begin match !curr with 
    Some v -> print_endline "Ok curr" ;
    | None -> print_endline "Not okie dokie" ; raise Exit
    end ; *)
    (srecord).leaf <- Option.get !curr ;
    (* try Option.get !curr with 
    Invalid_argument _ -> let _ = print_endline "!curr is None" in Option.get !curr ; *)

    (* Update other variables used in traversal *)
    parent_field := !curr_field ;
    let cmpval = 
      begin match (Option.get !curr).key with 
        | None -> -1 (* None represents infinity *)
        | Some v -> tree.compare key v 
      end in 
    (* let _ = begin match !curr with 
    Some v -> print_endline "Ok curr 2" ;
    | None -> print_endline "Not okie dokie 2" 
    end in  *)
    if cmpval = -1 then curr_field := Atomic.get (Option.get !curr).lchild
    else curr_field := Atomic.get (Option.get !curr).rchild ;

    curr := !curr_field.address
  done ;
  srecord ;
end

let search (tree : 'elt t) (key : 'elt) = 
begin

  let sR = seek key tree in  
  let cmpval = 
    match (sR.leaf).key with 
    | None -> false (* None represents infinity, doesn't match with any key *)
    | Some v -> (tree.compare v key = 0)
  in cmpval 
end

let cleanup (key : 'elt) (tree : 'elt t) (srecord : 'elt seek_record) = 
begin
  (*retrieve all the addresses stored in the seek record for easy access*)
  let anc = srecord.ancestor in
  let suc = srecord.successor in
  let par = srecord.parent in
  let leaf = srecord.leaf in
  (*obtain the address on which the atomic instructions will be executed*)
  (*first obtain the address of the field of the ancestor node that will be modified*)
  let succ_addr = 
    begin
      match anc.key with
      | None -> anc.lchild (* None represents inf, greater than everything*)
      | Some v -> 
        let cmpval = tree.compare key v in
        if cmpval < 0 then anc.lchild else anc.rchild
    end in
  (*obtain the addresses of the child fields of the parent node*)
  let child_addr, sib_addr = 
    begin
      match par.key with
      | None -> par.lchild, par.rchild
      | Some v ->
        let cmpval = tree.compare key v in
        if cmpval < 0 then par.lchild, par.rchild else par.rchild, par.lchild
    end in
  
  let {flag;_} = Atomic.get child_addr in

  if not flag then 
    (*the leaf node is not flagged for deletion; thus the sibling node must be marked for deletion*)
    (*switch the sibling address*)
    Atomic.set sib_addr (Atomic.get child_addr);
  (*tag the sibling edge; no modify operation can occur at this edge now*)
  (*this is the BTS instr*)
  (* let new_val = match Atomic.get sib_addr with {flag; tag; address} -> {flag; tag = true; address} in *)
  Atomic.set sib_addr {flag = (Atomic.get sib_addr).flag ; tag = true ; address = (Atomic.get sib_addr).address};

  (*read the flag and address fields*)
  (* let {flag; address; _} = Atomic.get sib_addr in *)
  (*the flag field will be copied to the new edge that will be created*)
  (*make sibling node a direct child of the ancestor node*)
  let old_val = Atomic.get succ_addr in
  if ((old_val.address <> Some suc) || (old_val.tag) || (old_val.flag)) 
  then false
  else 
    begin
      (* let new_val = {flag = flag; tag = false; address = address}  *)
      let check_val = Atomic.get sib_addr in
      let new_val = {flag = (Atomic.get sib_addr).flag ; tag = false ; address = (Atomic.get sib_addr).address} in
      if((check_val.address <> (Atomic.get par.rchild).address)) then false else
      Atomic.compare_and_set succ_addr old_val new_val
    end
end

let insert (tree : 'elt t) (key : 'elt) = 
begin
  let rec loop () = 
    let sR = seek key tree in 
    let par = (sR).parent in 
    let leaf = (sR).leaf in 
    let cmpval = 
      begin match leaf.key with 
        | None -> false (* None represents infinity, doesn't match with any key *)
        | Some v -> tree.compare key v = 0 
      end in 
    
    if cmpval then () (* Duplicate key *)
    else (* Key not present *)
      begin
        let child_addr = 
          begin match par.key with 
            | None -> par.lchild (* None represents infinity > all finite keys *)
            | Some v -> 
              let cmpval = tree.compare key v in 
              if cmpval < 0 then par.lchild else par.rchild 
          end in     

        (* Preliminary value for CAS *)
        let old_val = Atomic.get child_addr in 
          begin
            (* Create internal node and new leaf node *)
            let new_leaf =  ({
              key = Some key ;
              lchild = Atomic.make {flag = false; tag = false; address = None} ; 
              rchild = Atomic.make {flag = false; tag = false; address = None}
            }) in       
            
            let new_internal = {
              key = None ; 
              lchild = Atomic.make {flag = false; tag = false; address = None} ;
              rchild = Atomic.make {flag = false; tag = false; address = None}
            } in 

            let cmpval = 
              begin match leaf.key with 
                | None -> -1
                | Some v -> tree.compare key v
              end in 
            
            if cmpval < 0 then 
              begin
                Atomic.set new_internal.lchild {
                  flag = false; tag = false; address = Some (new_leaf)
                } ;
                Atomic.set new_internal.rchild {
                  flag = false; tag = false; address = Some leaf
                } ;
                new_internal.key <- leaf.key ;
              end
            else 
              begin
                Atomic.set new_internal.lchild {
                  flag = false; tag = false; address = Some leaf
                } ;
                Atomic.set new_internal.rchild {
                  flag = false; tag = false; address = Some (new_leaf)
                } ;
                new_internal.key <- Some key ;
              end ;
            let new_val = {
              flag = false ;
              tag = false ; 
              address = Some new_internal ;
            } in 

            if (not(Option.get old_val.address == leaf)) || old_val.flag || old_val.tag then
              begin 
              if (Option.get old_val.address = leaf) && (old_val.flag || old_val.tag) 
                then ignore(cleanup key tree sR) ;(* Structurally need to check since CAS does physical equality. CAS(child_addr , {0 ; 0 ; leaf} , new_val) *)
              loop ()
              end
            else 
            let result = Atomic.compare_and_set child_addr old_val new_val in 

            if result then () (* Insert success *)
            else (* Insert failed, help the conflicting delete operation *)
              begin
                let {flag ; tag ; address} = Atomic.get child_addr in 
                if (address = Some leaf) && (flag || tag) then 
                  (* Address has not changed but sibling/leaf has been flagged for deletion *)
                  ignore(cleanup key tree sR) ; 
                loop ()
              end
          end
      end in 
  loop ()
end

let delete (tree : 'elt t) (key : 'elt) = 
begin 
  let mode = ref 0 in (* 0 = Injection Mode , 1 = Cleanup mode *)
  let leaf = ref tree.nodeS in
  let rec loop () = 
    let sR = seek key tree in 
    let par = sR.parent in 
    let child_addr = 
      begin match par.key with 
        | None -> par.lchild (* None represents infinity > all finite keys *)
        | Some v -> 
          let cmpval = tree.compare key v in 
          if cmpval < 0 then par.lchild else par.rchild 
      end in 
    
    if !mode = 0 then
      (* Injection mode: Check if the key is present in the tree  *)
      let _ = leaf := (sR.leaf) in
      begin match !leaf.key with 
        | None -> false (* None represents infinity , Key not present *)
        | Some v -> 
          if tree.compare key v != 0 then false (* Key not present *)
          else 
            begin
              let new_val = {
                flag = true ;
                tag = false ;
                address = Some !leaf
              } in 
              let old_val = Atomic.get child_addr in 
              if (not(Option.get old_val.address == !leaf)) || (old_val.tag) || (old_val.flag) then 
                begin
                if (Option.get old_val.address = !leaf) && (old_val.tag || old_val.flag) 
                  then cleanup key tree sR
                  else loop () 
                end
              else 
                begin 
                  let result = Atomic.compare_and_set child_addr old_val new_val in 
                  if result then 
                    begin 
                      (* Advance to the cleanup mode and try to remove the leaf node from the tree *)
                      mode := 1 ; 
                      let clean_done = cleanup key tree sR in 
                      if clean_done then true else loop () 
                    end
                  else 
                    begin
                      let {flag ; tag ; address} = Atomic.get child_addr in 
                      if (address = Some !leaf) && (flag || tag) 
                        then cleanup key tree sR (* Address has not changed but sibling/leaf has been flagged for deletion -> Cleanup *)
                      else loop ()
                    end
                end 
            end
      end 
    else 
      (* Cleanup mode - Check if the leaf node that was flagged in the injection mode is still present in the tree *) 
      begin 
        if sR.leaf <> !leaf then false (* Leaf node is no longer present *)
        else 
          (* Leaf node is still present in the tree ; Remove it *)
          let clean_done = cleanup key tree sR in 
          if clean_done then true else loop () 
      end
  in 
  loop ()      
end
let remove tree key = delete tree key 
let add tree key = insert tree key 
let find tree key = search tree key 

let print_child child (printfn : 'elt -> unit) = 
  match child with
  {flag; tag; address} -> (
    if flag then print_string "true " else print_string "false ";
    if tag then print_string "true " else print_string "false ";
    match address with
    | None -> print_endline "null address"
    | Some v -> let {key:_} = v in match key with | None -> print_endline "inf" | Some x -> printfn x; print_endline "";  
  )

let print_node node (printfn : 'elt -> unit) =
  let {key; lchild; rchild} = node in
  (
    match key with
  | None -> print_endline "inf"
  | Some x -> printfn x; print_endline ""
  );
  print_string "lchild: "; print_child (Atomic.get lchild) printfn;
  print_string "rchild: "; print_child (Atomic.get rchild) printfn;
  ()

let print_srec srec (printfn : 'etl -> unit) = 
  match srec with {ancestor; successor; parent; leaf} -> (
    print_string "ancestor "; print_node ancestor printfn;
    print_string "successor "; print_node successor printfn;
    print_string "parent "; print_node parent printfn;
    print_string "leaf "; print_node leaf printfn;
  )

let to_plist tree = 
  let rec inorder_helper node acc depth = 
    let left = Atomic.get node.lchild in 
    let right = Atomic.get node.rchild in 

    begin match left.address , right.address with 
      | None , None -> 
        begin match node.key with 
        | None -> acc 
        | Some v -> (v, depth) :: acc 
        end 
      | Some lnode , None -> inorder_helper lnode acc (depth + 1)
      | None , Some rnode -> inorder_helper rnode acc (depth + 1)
      | Some lnode , Some rnode -> 
        let leftacc = inorder_helper lnode acc (depth + 1) in 
        inorder_helper rnode leftacc (depth + 1)
    end in 
    inorder_helper (tree.root) [] 0

let print_tree (tree : 'elt t) (printfn : 'elt -> unit) = 
  let rec traverse node depth = 
    (* Print current node information *)
    print_string "Depth "; print_int depth; print_string ": ";
    print_node node printfn;
    print_endline "---";
    
    (* Get children *)
    let left = Atomic.get node.lchild in 
    let right = Atomic.get node.rchild in 
    
    (* Traverse left child if it exists *)
    (match left.address with 
     | None -> ()
     | Some lnode -> traverse lnode (depth + 1)
    );
    
    (* Traverse right child if it exists *)
    (match right.address with 
     | None -> ()
     | Some rnode -> traverse rnode (depth + 1)
    )
  in 
  print_endline "=== Tree Structure ===";
  traverse tree.root 0;
  print_endline "Print complete"

(* 
let print_tree (tree : 'elt t) (printfn : 'elt -> unit) = 
  let list = to_plist tree in
  List.iter (fun (a, b) -> print_string "("; printfn a; print_string ", "; print_int b; print_endline ")") list ; print_endline "Print complete"  *)
let to_list tree = 
  let rec inorder_helper node acc = 
    let left = Atomic.get node.lchild in 
    let right = Atomic.get node.rchild in 

    begin match left.address , right.address with 
      | None , None -> 
        begin match node.key with 
        | None -> acc 
        | Some v -> v :: acc 
        end 
      | Some lnode , None -> inorder_helper lnode acc 
      | None , Some rnode -> inorder_helper rnode acc 
      | Some lnode , Some rnode -> 
        let leftacc = inorder_helper lnode acc in 
        inorder_helper rnode leftacc 
    end in 
  let leaves = inorder_helper (tree.root) [] in 
  List.sort tree.compare leaves 
 *)

module Atomic = Multicore_magic.Transparent_atomic 

module Stamped_Atomic =  struct

  type 'elt version = {
    value : 'elt ;
    stamp : int ;
  }

  type 'elt t = 'elt version Atomic.t 

  let make ?(stamp = 0) (value : 'elt) = 
    Atomic.make {value = value ; stamp = stamp} 

  let get_reference (version : 'elt t) = 
    (Atomic.get version).value 

  let get_stamp (version : 'elt t) =
    (Atomic.get version).stamp 

  let get (version : 'elt t) = 
    (Atomic.get version)

  let compare_and_set (curr_version : 'elt t) (old_val : 'elt) (new_val : 'elt) (old_stamp : int) (new_stamp : int) = 
    let old_version = Atomic.get curr_version in 
    if (old_version.value = old_val) && (old_version.stamp = old_stamp) then
      let new_version = {
        value = new_val  ;
        stamp = new_stamp ;
      } in 
      Atomic.compare_and_set curr_version old_version new_version 
    else false   

  let attempt_stamp (curr_version : 'elt t) (old_val : 'elt) (new_stamp : int) = 
    let old_version = Atomic.get curr_version in 
    if (old_version.value = old_val) then 
      let new_version = {
        value = old_val ; 
        stamp = new_stamp ;
      } in 
      Atomic.compare_and_set curr_version old_version new_version
    else false 
end


type 'elt node = {
  key : 'elt option ; (* Using option to differentiate finite and infinite value keys for implementation purposes *)
  lchild : 'elt node option Stamped_Atomic.t ;
  rchild : 'elt node option Stamped_Atomic.t
}

type 'elt seek_record = {
  ancestor : 'elt node option ; (* Using option to differentiate Null nodes and Non-null nodes *)
  successor : 'elt node option ;
  parent : 'elt node option ;
  leaf : 'elt node option ;
}

type 'elt t = {
  compare : ('elt -> 'elt -> int) ;
  nodeR : 'elt node option ;
  nodeS : 'elt node option ;
}

let to_plist tree =
  let rec inorder_helper node depth acc =
    let left = Stamped_Atomic.get_reference node.lchild in
    let right = Stamped_Atomic.get_reference node.rchild in
    
    match left, right with 
    | None, None -> 
      begin match node.key with
      | None -> acc
      | Some v -> acc @ [(v, depth)]
      end
    | Some lnode, None -> inorder_helper lnode (depth + 1) acc
    | None, Some rnode -> inorder_helper rnode (depth + 1) acc
    | Some lnode, Some rnode ->
      begin
        let leftacc = inorder_helper lnode (depth + 1) acc in
        inorder_helper rnode (depth + 1) leftacc
      end
    in
  inorder_helper (Option.get (tree.nodeR)) 0 []

let to_list tree = List.fold_left (fun acc (x, _) -> acc @ [x]) [] (to_plist tree)

let create ~(compare:'elt -> 'elt -> int) () = 
begin
  let nodeS = {
    key = None ; 
    lchild = Stamped_Atomic.make (Some {
      key = None ;
      lchild = Stamped_Atomic.make None ;
      rchild = Stamped_Atomic.make None ;
    }) ;
    rchild = Stamped_Atomic.make (Some {
      key = None ;
      lchild = Stamped_Atomic.make None ;
      rchild = Stamped_Atomic.make None ;
    }) ;
  } in 
  let nodeR = {
    key = None ; 
    lchild = Stamped_Atomic.make (Some nodeS) ; 
    rchild = Stamped_Atomic.make (Some {
      key = None ;
      lchild = Stamped_Atomic.make None ;
      rchild = Stamped_Atomic.make None ;
    }) ;
  } in 

  let tree = {
    compare = compare ; 
    nodeR = Some nodeR ;
    nodeS = Some nodeS ;
  } in tree
end

let seek (tree : 'elt t) (key : 'elt) = 
begin
  let parent_field = ref ((Option.get tree.nodeR).lchild) in 
  let curr_field = ref (Option.get tree.nodeS).lchild in 
  let cur_anc = ref tree.nodeR in 
  let cur_par = ref tree.nodeS in 
  let cur_succ = ref tree.nodeS in 
  let cur_leaf = ref ((Stamped_Atomic.get_reference (Option.get tree.nodeS).lchild)) in 

  let rec locate () = 
    if (Stamped_Atomic.get_reference !curr_field = None) then () 
    else 
        begin
        if (Stamped_Atomic.get_stamp !parent_field = 0) || (Stamped_Atomic.get_stamp !parent_field = 2) then
          begin
            cur_anc := !cur_par ;
            cur_succ := !cur_leaf ;
          end ;

        cur_par := !cur_leaf ;
        let curr = (Stamped_Atomic.get_reference !curr_field) in
        cur_leaf := curr ;
        parent_field := !curr_field ; 
        
        let cmpval = 
        begin match (Option.get curr).key with 
          | None -> -1 
          | Some v -> tree.compare key v 
        end in 
        if cmpval < 0 then curr_field := (Option.get curr).lchild else curr_field := (Option.get curr).rchild ;
        locate () 
      end
  in locate () ;
  let sR = {
    ancestor = !cur_anc ;
    successor = !cur_succ ;
    parent = !cur_par ;
    leaf = !cur_leaf ;
  } in 
  sR
end

let set_tag (stamp : int) = 
begin 
  if stamp = 0 then 1 (* 00 to 01 *)
  else if stamp = 2 then 3 (* 10 to 11 *)
  else stamp (* Tag bit is set already *)
end

let copy_flag (stamp : int) = 
begin 
  if stamp = 1 then 0 (* 01 to 00 *)
  else if stamp = 3 then 2 (* 11 to 10 *)
  else stamp (* Tag is toggled off already *)
end

let cleanup (tree : 'elt t) (key : 'elt) (sR : 'elt seek_record) =
begin 
  let ancestor = sR.ancestor in 
  let parent = sR.parent in 
  let sibling = ref None in 
  let sibling_stamp = ref 0 in 

  let cmpval = 
    begin match (Option.get parent).key with
    | None -> -1 
    | Some v -> tree.compare key v 
    end in
  
  if cmpval < 0 then 
    begin 
      if Stamped_Atomic.get_stamp (Option.get parent).lchild > 1 then 
        begin 
          sibling := Stamped_Atomic.get_reference (Option.get parent).rchild ;
          sibling_stamp := Stamped_Atomic.get_stamp (Option.get parent).rchild ;
          sibling_stamp := set_tag !sibling_stamp ;
          ignore (Stamped_Atomic.attempt_stamp (Option.get parent).rchild !sibling !sibling_stamp) ;
          sibling := Stamped_Atomic.get_reference (Option.get parent).rchild ;
          sibling_stamp := Stamped_Atomic.get_stamp (Option.get parent).rchild ;
        end
      else 
        begin 
          sibling := Stamped_Atomic.get_reference (Option.get parent).lchild ;
          sibling_stamp := Stamped_Atomic.get_stamp (Option.get parent).lchild ;
          sibling_stamp := set_tag !sibling_stamp ;
          ignore (Stamped_Atomic.attempt_stamp (Option.get parent).lchild !sibling !sibling_stamp) ;
          sibling := Stamped_Atomic.get_reference (Option.get parent).lchild ;
          sibling_stamp := Stamped_Atomic.get_stamp (Option.get parent).lchild ;
        end
    end
  else 
    begin 
      if Stamped_Atomic.get_stamp (Option.get parent).rchild > 1 then 
        begin 
          sibling := Stamped_Atomic.get_reference (Option.get parent).lchild ;
          sibling_stamp := Stamped_Atomic.get_stamp (Option.get parent).lchild ;
          sibling_stamp := set_tag !sibling_stamp ;
          ignore (Stamped_Atomic.attempt_stamp (Option.get parent).lchild !sibling !sibling_stamp) ;
          sibling := Stamped_Atomic.get_reference (Option.get parent).lchild ;
          sibling_stamp := Stamped_Atomic.get_stamp (Option.get parent).lchild ;
        end
      else 
        begin 
          sibling := Stamped_Atomic.get_reference (Option.get parent).rchild ;
          sibling_stamp := Stamped_Atomic.get_stamp (Option.get parent).rchild ;
          sibling_stamp := set_tag !sibling_stamp ;
          ignore (Stamped_Atomic.attempt_stamp (Option.get parent).rchild !sibling !sibling_stamp) ;
          sibling := Stamped_Atomic.get_reference (Option.get parent).rchild ;
          sibling_stamp := Stamped_Atomic.get_stamp (Option.get parent).rchild ;
        end
    end ;
  let cmpval = 
    begin match (Option.get ancestor).key with
    | None -> -1 
    | Some v -> tree.compare key v 
    end in 
  if cmpval < 0 then 
    begin 
      sibling_stamp := copy_flag !sibling_stamp ;
      (* let old_successor = Stamped_Atomic.get_reference (Option.get ancestor).lchild in
      let old_stamp = Stamped_Atomic.get_stamp (Option.get ancestor).lchild in *)
      let old_val = Stamped_Atomic.get (Option.get ancestor).lchild in 
      Stamped_Atomic.compare_and_set ((Option.get ancestor).lchild) old_val.value !sibling old_val.stamp !sibling_stamp 
    end
  else 
    begin 
      sibling_stamp := copy_flag !sibling_stamp ;
      (* let old_successor = Stamped_Atomic.get_reference (Option.get ancestor).rchild in *)
      let old_val = Stamped_Atomic.get (Option.get ancestor).rchild in 
      Stamped_Atomic.compare_and_set ((Option.get ancestor).rchild) old_val.value !sibling old_val.stamp !sibling_stamp 
    end
end

let insert (tree : 'elt t) (key : 'elt) = 
begin
  let rec loop () = 
    let nthChild = ref (-1) in 
    let pnode = ref tree.nodeS in 
    let node = ref ((Stamped_Atomic.get_reference (Option.get tree.nodeS).lchild)) in

    let rec locate () = 
      begin
        if (Stamped_Atomic.get_reference (Option.get !node).lchild = None) then ()
        else 
          begin
            let cmpval = 
            begin match (Option.get !node).key with 
              | None -> -1 
              | Some v -> tree.compare key v 
            end in 
            if cmpval < 0 then
              begin 
                pnode := (!node) ; 
                node := (Stamped_Atomic.get_reference ((Option.get !node).lchild)) ;
              end
            else 
              begin 
                pnode := (!node) ; 
                node := (Stamped_Atomic.get_reference ((Option.get !node).rchild)) ;
              end ;
            locate ()
          end
      end
    in locate () ;
    let old_child = (!node) in 
    let cmpval = 
    begin match (Option.get !pnode).key with 
      | None -> -1 
      | Some v -> tree.compare key v 
    end in 
    if cmpval < 0 then nthChild := 0 else nthChild := 1 ;
    let cmpval = 
      match (Option.get !node).key with
      | None -> false
      | Some v -> tree.compare v key = 0
    in
    if cmpval then () 
    else 
      let cmpval = 
      begin match (Option.get !node).key with 
      | None -> 1 
      | Some v -> tree.compare v key 
      end in 

      let leaf_node = {key = Some key ; lchild = Stamped_Atomic.make None ; rchild = Stamped_Atomic.make None} in 
      let internal_node = 
        if cmpval < 0 then Some {
          key = Some key ; 
          lchild = Stamped_Atomic.make !node ;
          rchild = Stamped_Atomic.make (Some leaf_node) ;
        } 
        else Some {
          key = (Option.get !node).key ;
          lchild = Stamped_Atomic.make (Some leaf_node) ;
          rchild = Stamped_Atomic.make !node ;
        } in 
      
      if !nthChild = 0 then 
        begin 
          let result = Stamped_Atomic.compare_and_set ((Option.get !pnode).lchild) old_child internal_node 0 0 in 
          if result then ()
          else 
            begin 
              if !node == Stamped_Atomic.get_reference (Option.get !pnode).lchild then 
                begin
                let sR = seek tree key in ignore(cleanup tree key sR) ;
                loop ()
                end
              else loop ()
            end 
        end
      else 
        begin
          let result = Stamped_Atomic.compare_and_set ((Option.get !pnode).rchild) old_child internal_node 0 0 in 
          if result then ()
          else 
            begin 
              if !node == Stamped_Atomic.get_reference (Option.get !pnode).rchild then 
                begin
                let sR = seek tree key in ignore(cleanup tree key sR) ;
                loop ()
                end
              else loop ()
            end 
        end 
  in loop ()     
end

let search (tree : 'elt t) (key : 'elt) = 
begin
  let node = ref tree.nodeR in 
  let rec locate () = 
    if Stamped_Atomic.get_reference (Option.get !node).lchild = None then () 
    else 
      begin
        let cmpval = 
          begin match (Option.get !node).key with 
          | None -> -1 
          | Some v -> tree.compare key v 
          end in 
        if cmpval < 0 then node := (Stamped_Atomic.get_reference (Option.get !node).lchild)
        else node := (Stamped_Atomic.get_reference (Option.get !node).rchild) ;
        locate ()
      end 
    in 
  locate () ;
  let cmpval = 
    begin match (Option.get !node).key with 
    | None -> false
    | Some v -> tree.compare key v = 0 
    end in 
  cmpval
end

let delete (tree : 'elt t) (key : 'elt) = 
begin 
  let is_cleanup = ref false in 
  let leaf = ref tree.nodeR in 
  let rec loop () = 
    let sR = seek tree key in 
    if not !is_cleanup then 
      begin 
        leaf := sR.leaf ;
        let cmpval = 
        begin match (Option.get !leaf).key with 
        | None -> false 
        | Some v -> tree.compare key v = 0 
        end in 
        if not cmpval then ()
        else 
          begin
            let parent = sR.parent in 
            let cmpval = 
              begin match (Option.get parent).key with 
              | None -> -1 
              | Some v -> tree.compare key v
              end in 
            if cmpval < 0 then 
              begin 
                let result = Stamped_Atomic.compare_and_set (Option.get parent).lchild !leaf !leaf 0 2 in 
                if result then 
                  begin 
                    is_cleanup := true ;
                    let clean_done = cleanup tree key sR in 
                    if clean_done then () else loop ()
                  end
                else 
                  begin 
                    if !leaf == Stamped_Atomic.get_reference (Option.get parent).lchild then ignore (cleanup tree key sR) ; 
                    loop ()
                  end
              end
            else
              begin
              let result = Stamped_Atomic.compare_and_set (Option.get parent).rchild !leaf !leaf 0 2 in 
              if result then 
                begin
                  is_cleanup := true ;
                  let clean_done = cleanup tree key sR in 
                  if clean_done then () else loop ()
                end   
              else 
                begin
                  if !leaf == Stamped_Atomic.get_reference (Option.get parent).rchild then ignore (cleanup tree key sR) ; 
                  loop ()
                end
              end 
          end
      end 
    else 
      begin 
        if sR.leaf == !leaf then 
          begin 
            let clean_done = cleanup tree key sR in 
            if clean_done then () else loop ()
          end 
        else ()
      end
  in 
  loop ()
end

      

