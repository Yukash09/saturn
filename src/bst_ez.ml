module Atomic = Multicore_magic.Transparent_atomic
type 'elt child = {
  flag : bool ;
  tag : bool ;
  address : 'elt node ref option ;
}

and 'elt node = {
  mutable key : 'elt option ;
  lchild : 'elt child Atomic.t ;
  rchild : 'elt child Atomic.t ;
}

type edge_type = 
| Left 
| Right 

type 'elt seek_record = {
  mutable ancestor : 'elt node ref ;
  mutable successor : 'elt node ref ;
  mutable parent : 'elt node ref ;
  mutable leaf : 'elt node ref ;
}

type 'elt t = {
  compare : 'elt -> 'elt -> int ;
  root : 'elt node ref ;
  nodeS : 'elt node ref ; 
  srecord : 'elt seek_record Domain.DLS.key 
}

let create ~compare () = 
begin 
  let leaf1 = {
    key = None ;
    lchild = Atomic.make {
      flag = false ;
      tag = false ;
      address = None ;
    } ;
    rchild = Atomic.make {
      flag = false ;
      tag = false ;
      address = None ;
    } ;
  } in 

  let leaf2 = {
    key = None ; 
    lchild = Atomic.make {
      flag = false ;
      tag = false ;
      address = None ;
    } ;
    rchild = Atomic.make {
      flag = false ;
      tag = false ;
      address = None ;
    } ;
  } in 

  let nodeS = {
    key = None ; 
    lchild = Atomic.make {
      flag = false ;
      tag = false ;
      address = Some (ref leaf1) ;
    } ;
    rchild = Atomic.make {
      flag = false ;
      tag = false ;
      address = Some (ref leaf2) ;
    } ;
  } in 

  let nodeR = {
    key = None ; 
    lchild = Atomic.make {
      flag = false ;
      tag = false ;
      address = Some (ref nodeS) ;
    } ;
    rchild = Atomic.make {
      flag = false ;
      tag = false ;
      address = None ;
    } ;
  } in 

  let srecord = Domain.DLS.new_key (fun () -> {
    ancestor = ref nodeR ;
    successor = ref nodeS ;
    parent = ref nodeS ;
    leaf = ref nodeR ;
  }) in 
  let tree = {
    compare = compare ;
    root = ref nodeR ;
    nodeS = ref nodeS ;
    srecord = srecord ;
  } in tree 
end
let seek (key : 'elt) (tree : 'elt t) = 
begin
  (* Initialize seek record using the sentinel nodes *)
  (Domain.DLS.get tree.srecord).ancestor <- tree.root ;
  (Domain.DLS.get tree.srecord).successor <- tree.nodeS ;
  (Domain.DLS.get tree.srecord).parent <- tree.nodeS ;  

  let left = Atomic.get !(tree.nodeS).lchild in 
  (Domain.DLS.get tree.srecord).leaf <- Option.get left.address ;

  (* Initialize other variables used in the traversal*)
  let parent_field = ref (Atomic.get !((Domain.DLS.get tree.srecord).parent).lchild) in 
  let curr_field = ref (Atomic.get !((Domain.DLS.get tree.srecord).leaf).lchild) in 
  let curr = ref !curr_field.address in 
  while !curr <> None do 
    (* Move down the tree, check if the edge from the (current) parent node in the access path is tagged *)

    if not !parent_field.tag then       
      (* Found an untagged edge in the access path, advance ancestor and successor pointers *)
    begin
      (Domain.DLS.get tree.srecord).ancestor <- (Domain.DLS.get tree.srecord).parent ;
      (Domain.DLS.get tree.srecord).successor <- (Domain.DLS.get tree.srecord).leaf ;
    end ;

    (* Advance parent and leaf pointers *)
    (Domain.DLS.get tree.srecord).parent <- (Domain.DLS.get tree.srecord).leaf ;
    (Domain.DLS.get tree.srecord).leaf <- Option.get !curr ;

    (* Update other variables used in traversal *)
    parent_field := !curr_field ;
    let cmpval = 
      begin match !(Option.get !curr).key with 
        | None -> -1 (* None represents infinity *)
        | Some v -> tree.compare key v 
      end in 
    
    if cmpval = -1 then curr_field := Atomic.get !(Option.get !curr).lchild
    else curr_field := Atomic.get !(Option.get !curr).rchild ;

    curr := !curr_field.address
  done
end

let search (tree : 'elt t) (key : 'elt) = 
begin

  seek key tree ; 
  let cmpval = 
    match !((Domain.DLS.get tree.srecord).leaf).key with 
    | None -> false
    | Some v -> (tree.compare v key = 0)
  in cmpval 
end

let cleanup (key : 'elt) (tree : 'elt t) = () 

let insert (tree : 'elt t) (key : 'elt) = 
begin
  let rec loop () = 
    seek key tree ; 
    let par = (Domain.DLS.get tree.srecord).parent in 
    let leaf = (Domain.DLS.get tree.srecord).leaf in 
    let cmpval = 
      begin match !leaf.key with 
        | None -> false 
        | Some v -> tree.compare key v = 0 
      end in 
    
    if cmpval then () (* Duplicate key *)
    else
      begin
        let child_addr = 
          begin match !par.key with 
            | None -> !par.lchild 
            | Some v -> 
              let cmpval = tree.compare key v in 
              if cmpval < 0 then !par.lchild else !par.rchild 
          end in     

        (* Preliminary value for CAS *)
        let old_val = Atomic.get child_addr in 
        
        if old_val.address <> Some leaf then loop () 
        else
          begin

            let new_leaf = ref ({
              key = Some key ;
              lchild = Atomic.make {flag = false; tag = false; address = None} ; 
              rchild = Atomic.make {flag = false; tag = false; address = None}
            }) in       
            
            let new_internal = ref {
              key = None ; 
              lchild = Atomic.make {flag = false; tag = false; address = None} ;
              rchild = Atomic.make {flag = false; tag = false; address = None}
            } in 

            let cmpval = 
              begin match !leaf.key with 
                | None -> -1
                | Some v -> tree.compare key v
              end in 
            
            if cmpval < 0 then 
              begin
                Atomic.set !new_internal.lchild {
                  flag = false; tag = false; address = Some (new_leaf)
                } ;
                Atomic.set !new_internal.rchild {
                  flag = false; tag = false; address = Some leaf
                } ;
                !new_internal.key <- !leaf.key ;
              end
            else 
              begin
                Atomic.set !new_internal.lchild {
                  flag = false; tag = false; address = Some leaf
                } ;
                Atomic.set !new_internal.rchild {
                  flag = false; tag = false; address = Some (new_leaf)
                } ;
                !new_internal.key <- Some key ;
              end ;
            let new_val = {
              flag = false ;
              tag = false ; 
              address = Some new_internal ;
            } in 
            if old_val.address <> Some leaf then loop () 
            else
            let result = Atomic.compare_and_set child_addr old_val new_val in 

            if result then () 
            else 
              begin
                let {flag ; tag ; address} = Atomic.get child_addr in 
                if (address = Some leaf) && (flag || tag) then 
                  cleanup key tree ; 
                loop ()
              end
          end
      end in 
  loop ()
end

let remove tree key = raise (failwith "Not implemented")
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
      | Some lnode , None -> inorder_helper !lnode acc 
      | None , Some rnode -> inorder_helper !rnode acc 
      | Some lnode , Some rnode -> 
        let leftacc = inorder_helper !lnode acc in 
        inorder_helper !rnode leftacc 
    end in 
  let leaves = inorder_helper !(tree.root) [] in 
  List.sort tree.compare leaves 

