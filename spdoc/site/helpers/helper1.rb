# An easy way is to put your helpers in the helpers directory
# and name them after their module (i.e., CustomHelpers lives in helpers/custom_helpers.rb).
# Then, Middleman will automatically load them and register them as helpers.

module ResourceTreeHelper
  def some_method
    # ...do something here...
  end

def resource_tree(paths)
    tree = {}
    paths.each do |path|
        parts = path.split('/')
        tree_node = tree
        parts.each do |part|
            tree_node[part] = {} unless tree_node.has_key?(part)
            tree_node = tree_node[part]
        end
    end
    tree
end

def print_hash(hash, indent=1)
    hash.each do |key,val|
        is_leaf = val.empty?
        mark = if is_leaf then "- " else "+ " end
        puts ("|   "*(indent-1)) + ("|---") + mark + key
        print_hash(val, indent + 1) unless is_leaf
    end
end

end
