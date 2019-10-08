'use strict';
var $update = function (r, lbl, v) {
  var ret = {};
  for (var k in Object.getOwnPropertyNames(r)) {
    ret[k] = r[k];
  }
  ret[lbl] = v;
  return ret;
};
var $lazy = function (f) {
  return { state: 'delayed', thunk: f };
};
var $force = function (l, k) {
  switch (l.state) {
    case 'ready':
      return k(l.thunk);
    case 'in-progress':
      throw 'Infinite loop';
    case 'delayed':
      l.state = 'in-progress';
      return l.thunk(function (val) {
        l.thunk = val;
        l.state = 'ready';
        return k(l.thunk);
      });
  }
};

var mule = function(){
  var call1 = function(f, v) {
    var result = null;
    var next = f(v, (r) => {
      result = r;
      return null;
    })
    while(result === null) {
      next = next()
    }
    return result;
  };

  var call = function(f) {
    for(var i = 1; i < arguments.length; i++) {
      f = call1(f, arguments[i]);
    }
    return f;
  };

  var exec = function() {
    return call(...arguments)()
  };

  var fn1 = (f) => (x, k) => k(f(x));

  var fn = (count, f) => {
    let ret = fn1(f);
    for(var i = 3; i < arguments; i++) {
      ret = (x, k) => () => k(f(x, fn1))
    }
    return ret;
  };

  return {
    call: call,
    exec: exec,
    fn: fn,
  }
}()

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
