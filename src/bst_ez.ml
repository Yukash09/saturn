module Atomic = Multicore_magic.Transparent_atomic

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
      address = None ; (* None represents infinity *)
    } ;
    rchild = Atomic.make {
      flag = false ;
      tag = false ;
      address = None ; (* None represents infinity *)
    } ;
  } in 

  let leaf2 = {
    key = None ; 
    lchild = Atomic.make {
      flag = false ;
      tag = false ;
      address = None ; (* None represents infinity *)
    } ;
    rchild = Atomic.make {
      flag = false ;
      tag = false ;
      address = None ; (* None represents infinity *)
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
      address = None ; (* None represents infinity *)
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
  let new_val = match Atomic.get sib_addr with {flag; tag; address} -> {flag; tag = true; address} in
  Atomic.set sib_addr new_val;

  (*read the flag and address fields*)
  let {flag; address; _} = Atomic.get sib_addr in
  (*the flag field will be copied to the new edge that will be created*)
  (*make sibling node a direct child of the ancestor node*)
  let old_val = Atomic.get succ_addr in
  if ((old_val.address <> Some suc) || (old_val.tag) || (old_val.flag)) then let _ = print_endline "This check failed" in false
  else 
    begin
      let new_val = {flag = flag; tag = false; address = address} in
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

            if (old_val.address <> Some leaf) || old_val.flag || old_val.tag 
              then loop () (* Structurally need to check since CAS does physical equality. CAS(child_addr , {0 ; 0 ; leaf} , new_val) *)
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
              if (old_val.address <> Some !leaf) || (old_val.tag) || (old_val.flag) then loop () 
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
      (* Cleanup mode - Check if the leaf node that was flgged in the injection mode is still present in the tree *) 
      begin 
        if sR.leaf <> !leaf then true (* Leaf node is no longer present *)
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

