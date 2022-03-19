let write_tbl_to_log tbl tbl_name=
  Log.debug ("Contents of " ^ tbl_name);
  Hashtbl.iter (fun k v -> Log.debug (Consts.fmt "%s -> %s" k v)) tbl; ()

let write_bool_tbl_to_log tbl tbl_name=
  Log.debug ("Contents of " ^ tbl_name);
  Hashtbl.iter (fun k v -> Log.debug (Consts.fmt "%s -> %b" k v)) tbl; ()

let write_list_to_log lst name = 
  Log.debug ("Contents of " ^ name);
  List.iter (fun l -> Log.debug l) lst; ()

let write_tbl_list_to_log tbl_lst name = 
    Log.debug ("Contents of " ^ name);
    List.iter (fun l -> write_tbl_to_log l "") tbl_lst; ()