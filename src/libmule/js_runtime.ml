
let src = "'use strict';
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

const $force = (l) => {
	switch(l.state) {
	case 'ready':
			return l.thunk;
	case 'in-progress':
			throw 'Infinite loop';
	case 'delayed':
			l.state = 'in-progress';
			l.thunk = l.thunk();
			l.state = 'ready';
			return l.thunk;
	}
}
"
