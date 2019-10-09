type ('m, 'a) t =  {
  meta: 'm;
  data: 'a;
}

let map_data wm ~f =
  { wm with data = f wm.data }

let map_meta wm ~f =
  { wm with meta = f wm.meta }
