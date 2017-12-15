# An easy way is to put your helpers in the helpers directory
# and name them after their module (i.e., CustomHelpers lives in helpers/custom_helpers.rb).
# Then, Middleman will automatically load them and register them as helpers.

module ResourceTreeHelper

# Each item in the tree is {key, valHash}, where valHash is empty,
# if it is a leaf. This way we can build a tree by always
# inserting new item into node Hash.
#
def resource_tree(resources=sitemap.resources, strip_prefix='pages/')
    tree = {}
    resources.each do |resource|
        parts = resource.destination_path.partition(strip_prefix)[2].split('/')
        tree_node = tree
        parts.each do |part|
            key = if part.equal?(parts.last) then resource else part end
            tree_node[key] = {} unless tree_node.has_key?(key)
            tree_node = tree_node[key]
        end
    end
    tree
end

# hash is output of resource_tree and its type is Hash 
def print_resource_tree(hash, ul='<ul>', indent=0, href_target='')
    output = ""
    hash.each do |key,val|
        is_leaf = val.empty?
        if is_leaf
            path = key.destination_path #TODO use key.url
            title = key.data.title || path
            output << (' '*indent) + "<li>" +
                "<a href=\"/#{path}\" #{href_target}>" + title + "</a>" + "</li>"> + "\n"
        else
            folder_name = key.gsub('_',' ').gsub(/\b\w/, &:capitalize)
            output << (' '*indent) + "<li>" + '<a href="#">' + folder_name + '</a>' + "\n"
            output << (' '*indent) + ul + "\n"
            output << print_resource_tree(val, ul, indent + 4)
            output << (' '*indent) + "</ul></li>\n"
        end
    end
    output
end

end
