var $mulecp = function(old, updates) {
	var copy = function(dst, src) {
		var props = Object.getOwnPropertyNames(src)
		for(var i = 0; i < props.length; i++) {
			var p = props[i]
			dst[p] = src[p]
		}
	}
	var ret = {}
	copy(ret, old)
	copy(ret, updates)
	return ret
}
