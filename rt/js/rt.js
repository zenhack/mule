
const $update = (r, lbl, v) => {
	var ret = {};
	for(var k in Object.getOwnPropertyNames(r)) {
		ret[k] = r[k];
	}
	ret[lbl] = v;
	return ret;
}
