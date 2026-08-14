namespace IronKernel

module Choice =
    
    let returnM = Choice2Of2

    let bind f = 
        function
        | Choice2Of2 x -> f x
        | Choice1Of2 x -> Choice1Of2 x

    type EitherBuilder() =
        member this.Return a = returnM a
        member this.Bind(m,f) = bind f m
        member this.ReturnFrom(o) = o

    let either = new EitherBuilder()

    let rec fold f zero = function
        | [] -> returnM zero
        | x::tail -> either {
                        let! acc = f zero x
                        return! fold f acc tail
                     }

module List =
   
   let rec skip n xs = 
      match (n, xs) with
      | 0, _ -> xs
      | _, [] -> []
      | n, _::xs -> skip (n-1) xs

   let foldl1 f lst = 
       match lst with
        | [] -> failwith "Empty_list"
        | x::xs -> List.fold f x xs

   let rec last = function
        | hd :: [] -> hd
        | hd :: tl -> last tl
        | _ -> failwith "Empty list."
