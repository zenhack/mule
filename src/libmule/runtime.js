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

const mule = {
	call: $call,
	exec: $exec,
	fn: $fn,
}
