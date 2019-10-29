'use strict';
var js = function() {
  var from_value = (v) => () => {
    var type = typeof(v);
    switch(type) {
    case 'bigint':
      return ['Int', v];
    case 'number':
      return ['Number', v]
    case 'string':
      return ['Text', v];
    case 'undefined':
        return ['Undefined', v];
    case 'object':
        if(v === null) {
          return ['Null', v];
        }
        return ['Object', v];
    default:
      return ['Unknown', v];
    }
  }
  var to_int = (v) => () => BigInt(v|0)
  return {
    'reflect': mule.fn(1, from_value),
    'as-int': mule.fn(1, to_int),

    'get-prop': mule.fn(2, (o) => (p) => () => o[p]),
    'set-prop': mule.fn(3, (o) => (p) => (v) => () => {
        o[p] = v;
        return {};
    }),

    'just': mule.fn(1, (v) => () => v),
    'then': mule.fn(2, (x) => (f) => () => mule.exec(f, x())),
  }
}

var root_io = {
  'just': js.just,
  'then': js.then,

  'print': mule.fn(1, (s) => () => {
    console.log(s);
    return {};
  }),

  'get-line': () => "TODO",
}
