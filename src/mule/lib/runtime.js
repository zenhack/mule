'use strict';
const $update = (r, lbl, v) => {
  var ret = {};
  for(var k in Object.getOwnPropertyNames(r)) {
    ret[k] = r[k];
  }
  ret[lbl] = v;
  return ret;
}

const $lazy = (f) => {
  return {state: 'delayed', thunk: f}
}

const $force = (l, k) => {
  switch(l.state) {
  case 'ready':
    return () => k(l.thunk);
  case 'in-progress':
    throw 'Infinite loop';
  case 'delayed':
    l.state = 'in-progress';
    return l.thunk((val) => {
      l.thunk = val;
      l.state = 'ready';
      return k(l.thunk);
    })
  }
}

const $fn1 = (f) => (x, k) => () => k(f(x))
const $fn2 = (f) => (l, k) => () => k((r, k) => () => k(f(l, r)))
const $fn3 = (f) => (x, k) => () => k((y, k) => () => k((z, k) => () => k(f(x, y, z))))

const int = {
  add: $fn2((x, y) => x + y),
  sub: $fn2((x, y) => x - y),
  mul: $fn2((x, y) => x * y),
  div: $fn2((x, y) => x / y),
  rem: $fn2((x, y) => x % y),
}

const char = {}

const text = {
  length: $fn1((x) => x.length),
  append: $fn2((x, y) => x + y),
  uncons: $fn1((x) => {
    if(x.length === 0) {
      return ['None', {}]
    } else {
      return ['Some', {
        head: x[0],
        tail: x.slice(1),
      }]
    }
  }),
  'from-int': $fn1(String),
}

const $call1 = function(f, v) {
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

const $call = function(f) {
	for(var i = 1; i < arguments.length; i++) {
		f = $call1(f, arguments[i]);
	}
	return f;
};

const $exec = function() {
	return $call(...arguments)()
};

const $fn = (count, f) => {
	let ret = $fn1(f);
	for(var i = 3; i < arguments; i++) {
		ret = (x, k) => () => k(f(x, $fn1))
	}
	return ret;
};

const $js = {
	'get-prop': $fn2((prop, obj) => () => obj[prop]),
	'set-prop': $fn3((prop, val, obj) => () => {
		obj[prop] = val
		return {}
	}),
	'int': $fn1((x) => x),
	'text': $fn1((x) => x),

	'function': $fn1((f) => () => {
		return $call1(f, arguments)
	}),
	'null': null,
	'undefined': undefined,

	'reflect': $fn1((v) => () => {
			var type = typeof(v)
			switch(type) {
			case 'bigint':
				return ['Int', v]
			case 'number':
				return ['Number', v]
			case 'string':
				return ['Text', v]
			case 'undefined':
					return ['Undefined', v]
			case 'object':
					if(v === null) {
						return ['Null', v]
					}
					return ['Object', v]
			default:
				return ['Unknown', v]
		}
	}),

	'call': $fn2((f, args) => () => f(...args)),
	'call1': $fn2((f, arg) => () => f(arg)),
	'call0': $fn1((f) => () => f()),
	'try': $fn1((cmd) => () => {
		try {
			return ['Ok', cmd()]
		} catch(e) {
			return ['Err', e]
		}
	}),
	'throw': $fn1((x) => () => { throw(x) }),
	'finally': $fn2((cmd, cleanup) => () => {
			try {
				return cmd()
			} finally {
				cleanup()
			}
	}),

	'just': $fn1((x) => () => x),
	'then': $fn2((x, f) => () => $call1(f, x())()),
}

const mule = {
	js: $js,
	call: $call,
	exec: $exec,
	fn: $fn,
}
