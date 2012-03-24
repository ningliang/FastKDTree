// node: { data: obj, coords: [...] }
// search_state: priority_queue
var FastKDTree = klass(function(bucket_size) {
  this.bucket_size = bucket_size || 10;
  this.nodes = [];

  // tree state
  this.left = null;
  this.right = null;
  this.mean = null;
  this.sum_sq_dev = null;
  this.singularity = true;
  this.content_max = null;
  this.content_min = null;
  this.split_dim = 0;
  this.split = null;
})

.methods({
  is_tree: function() {
    return this.left != null
  },

  dimensions: function() {
    return this.content_max.length;
  },

  add: function(node) {
    this.add_all([node])
  },

  add_all: function(nodes) {
    var trees = [];
    for (var i in nodes) {
      var node = nodes[i];
      var tree = FastKDTree.add_no_split(this, node);
      trees.push(tree)
    }

    trees = _.uniq(trees);
    for (var index in trees) {
      var tree = trees[index];
      if (FastKDTree.should_split(tree)) {
        FastKDTree.split(tree);
      }
    }
  },

  k_nearest: function(coords, k) {
    return FastKDTree.k_nearest(this, coords, k);
  },

  is_empty: function() {
    return this.content_min == null;
  }
})

.statics({
  add_no_split: function(tree, node) {
    cursor = tree;
    while (cursor != null) {
      FastKDTree.update_bounds(cursor, node);
      if (cursor.is_tree()) {
        // sub tree
        cursor = node.coords[cursor.split_dim] <= cursor.split ? cursor.left : cursor.right;
      } else {
        // leaf
        cursor.nodes.push(node);
        var num = cursor.nodes.length;
        var dims = cursor.dimensions();
        if (num == 1) {
          cursor.mean = _.clone(node.coords);
          cursor.sum_sq_dev = [];
        } else {
          // update running mean and sum_sq_dev
          for (var d = 0; d < dims; d++) {
            var coord = node.coords[d];
            var old_mean = cursor.mean[d];
            var new_mean = old_mean + (coord - old_mean) / num;
            cursor.mean[d] = new_mean;
            cursor.sum_sq_dev[d] = cursor.sum_sq_dev[d] + (coord - old_mean) * (coord - new_mean);
          }
        }

        if (cursor.singularity) {
          var nodes = cursor.nodes;
          if (nodes.length > 0 && !_.isEqual(node.coords, nodes[0].coords)) {
            cursor.singularity = false;
          }
        }

        return cursor;
      }
    }
    throw "Walked tree without adding anything.";
  },

  update_bounds: function(tree, node) {
    var dims = node.coords.length;
    if (tree.content_max == null) {
      tree.content_max = _.clone(node.coords);
      tree.content_min = _.clone(node.coords);
    } else {
      for (var d = 0; d < dims; d++) {
        var dim_val = node.coords[d];
        if (dim_val > tree.content_max[d]) {
          tree.content_max[d] = dim_val;
        } else if (dim_val < tree.content_min[d]) {
          tree.content_min[d] = dim_val;
        }
      }
    }
  },

  should_split: function(tree) {
    return tree.nodes.length > tree.bucket_size && !tree.singularity;
  },

  split: function(tree) {
    if (tree.singularity) {
      throw "Can't split singular tree."
    }

    // find the dimension with greatest variance
    var largest_variance = -1;
    var split_dim = 0;
    for (var d = 0; d < tree.dimensions(); d++) {
      var variance = tree.sum_sq_dev[d];
      if (variance > largest_variance) {
        largest_variance = variance;
        split_dim = d;
      }
    }

    // split on the dimension with greatest variance
    var split_value = tree.mean[split_dim];
    var left_nodes = [];
    var right_nodes = [];
    tree.nodes.forEach(function(node) {
      if (node.coords[split_dim] <= split_value) {
        left_nodes.push(node)
      } else {
        right_nodes.push(node);
      }
    });

    // if completely unbalanced, randomly split
    var left_size = left_nodes.length;
    var tree_size = tree.nodes.length;
    while (left_size == tree_size || left_size == 0) {
      left_nodes = [];
      right_nodes = [];
      split_dim = Math.floor(Math.random() * tree.dimensions());
      var split_pt_index = Math.floor(Math.random() * tree.nodes.length);
      split_value = tree.nodes[split_pt_index].coords[split_dim];
      tree.nodes.forEach(function(node) {
        if (node.coords[split_dim] <= split_value) {
          left_nodes.push(node);
        } else {
          right_nodes.push(node);
        }
      });
      left_size = left_nodes.length;
    }

    // build subtrees
    var left = new FastKDTree(tree.bucket_size);
    var right = new FastKDTree(tree.bucket_size);
    left.add_all(left_nodes);
    right.add_all(right_nodes);

    // save split parameters at current tree node
    tree.split_dim = split_dim;
    tree.split = split_value;
    tree.left = left;
    tree.right = right;

    // tree is now an intermediate node
    tree.data = [];
    tree.mean = tree.sum_sq_dev = null;
  },

  // search_stack_entry: { tree: tree, needs_bounds_check: boolean }
  k_nearest: function(tree, coords, k) {
    var state = new PriorityQueue(k);
    var stack = [];

    // check that the tree isn't empty
    if (tree.content_min != null) {
      stack.push({ tree: tree, needs_bounds_check: false });
    }

    while (stack.length != 0) {
      var entry = stack.pop();
      var curr_tree = entry.tree;
      if (entry.needs_bounds_check && state.size() >= k) {
        var d = FastKDTree.min_dist_sq_from(coords, curr_tree.content_min, curr_tree.content_max);
        if (d > state.last().priority) {
          continue;
        }
      }

      if (curr_tree.is_tree()) {
        FastKDTree.search_tree(curr_tree, coords, stack);
      } else {
        FastKDTree.search_leaf(curr_tree, coords, state);
      }
    }

    return state.nodes();
  },

  // enqueues subtrees based on how close they are
  search_tree: function(tree, coords, stack) {
    var near_tree = tree.left;
    var far_tree = tree.right;
    if (coords[tree.split_dim] > tree.split) {
      far_tree = tree.left;
      near_tree = tree.right;
    }

    if (!far_tree.is_empty()) {
      stack.push({ tree: far_tree, needs_bounds_check: true });
    }

    if (!near_tree.is_empty()) {
      stack.push({ tree: near_tree, needs_bounds_check: false });
    }
  },

  search_leaf: function(leaf, coords, state) {
    var dist = null;
    leaf.nodes.forEach(function(node) {
      if (!leaf.singularity || dist == null) {
        dist = FastKDTree.dist_sq(coords, node.coords);
      }

      if (state.size() < state.max_size() || dist < state.last().priority) {
        state.insert(node, dist)
      }
    });
  },

  dist_sq: function(left, right) {
    var sum_sq = 0.0;
    for (var d = 0; d < left.length; d++) {
      var dist = left[d] - right[d];
      if (dist != 0) {
        sum_sq += dist * dist;
      }
    }
    return sum_sq;
  },

  min_dist_sq_from: function(target, min, max) {
    var dist_sq = 0;
    for (var d = 0; d < target.length; d++) {
      if (target[d] < min[d]) {
        var dist = min[d] - target[d];
        dist_sq += dist * dist;
      } else if (target[d] > max[d]) {
        var dist = max[d] - target[d];
        dist_sq += dist * dist;
      }
    }
    return dist_sq;
  }
});

var PriorityQueue = klass(function(k) {
  this._priority_nodes = [];
  this._k = k;
})
.methods({
  insert: function(node, priority) {
    var inserted = false;
    for (var i = 0; i < this._priority_nodes.length; i++) {
      if (priority <= this._priority_nodes[i].priority) {
        this._priority_nodes.splice(i, 0, { node: node, priority: priority });
        inserted = true;
        break;
      }
    }

    if (!inserted && this._priority_nodes.length < this._k) {
      this._priority_nodes.push({ node: node, priority: priority });
    }

    while (this._priority_nodes.length > this._k) {
      this._priority_nodes.pop();
    }
  },

  peek: function() {
    return this._priority_nodes[0];
  },

  last: function() {
    return this._priority_nodes[this._priority_nodes.length - 1];
  },

  poll: function() {
    return this._priority_nodes.shift();
  },

  size: function() {
    return this._priority_nodes.length;
  },

  max_size: function() {
    return this._k;
  },

  nodes: function() {
    return this._priority_nodes.map(function(pn) { return pn.node; });
  }
})
