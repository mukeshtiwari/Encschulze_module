open Cryptobinding
open Big
open Lib

let print_pair (c1, c2) = "(" ^ Big.to_string c1 ^ ", " ^ Big.to_string c2 ^ ")"

let print_list f lst =
  let rec print_elements = function
    | [] -> ()
    | h  :: t -> print_string (f h); print_string ";"; print_elements t
  in
  print_string "[";
  print_elements lst;
  print_string "]";;


let cartesian l l' =
    List.concat (List.map (fun e -> List.map (fun e' -> (e,e')) l') l)

let rec cross_prod_orig l = cartesian l l

let l = ["A"; "B"; "C"]

let rec gen_ballot cand_pair evalue =
   match cand_pair, evalue with
   | [], [] -> ""
   | [(c1, c2)], [v] -> "("^ c1 ^ ", " ^ c2 ^ ", " ^ print_pair v ^ ")"
   | (c1, c2) :: tl, v :: vtl -> "("^ c1 ^ ", " ^ c2 ^ ", " ^ print_pair v ^ "); " ^ gen_ballot tl vtl

let () =
  let (grp, gen, pubkey) = construct_group (prime, generator, publickey) in
  (*let prikey = construct_private_key (group, generator, publickey) privatekey in *)
  let ballot = List.map (fun x -> encrypt_message grp gen pubkey (Big.of_string x)) ["0"; "10"; "1"; "-10"; "0"; "1"; "-1"; "-1"; "0"] in
  let decballot = List.map (fun x -> decrypt_message_binding grp gen prikey x) ballot in
  print_list print_pair ballot;
  print_newline ();
  print_list Big_integer.to_string decballot;
  print_newline ();
  print_endline (gen_ballot (cross_prod_orig l) ballot)


