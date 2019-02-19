var $mulecp = function(old, updates) {
	var ret = {}
	var oldProps = Object.getOwnPropertyNames(old)
	for(var i = 0; i < oldProps.length; i++) {
		var prop = oldProps[i]
		ret[prop] = old[prop]
	}
	var newProps = Object.getOwnPropertyNames(updates)
	for(var i = 0; i < newProps.length; i++) {
		var prop = newProps[i]
		ret[prop] = updates[prop]
	}
	return ret
}
