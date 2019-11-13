def get_intermediate_nodes(node1, cur_taxi, next_taxi):
    neighbors = neighbor(node1, cur_taxi) # neighbors will have length <= 2 unless the taxiway is self-intersecting
    node_list = intermediate_nodes(node1, node1, cur_taxi, next_taxi, neighbors[0])
    if node_list is None & len(neighbors) > 1:
        node_list = intermediate_nodes(node1, node1, cur_taxi, next_taxi, neighbors[1])
    return node_list

def intermediate_nodes(pre_node, cur_node, cur_taxi, next_taxi, neighbors):
    if neighbors == [] 
        return None
    else if head(heighbors) == pre_node:
        return intermediate_nodes(pre_node,cur_node, cur_taxi, next_taxi, rest(neighbors))
    else:
        if is_on_taxiway(head(neighbors),next_taxi) == true: 
            return head(neighbors)
        else
            return head(neighbors) :: intermediate_nodes(cur_node, head(neighbors), cur_taxi, next_taxi, neighbor(head(neighbors), cur_taxi))



#============================================================================


def get_last_segment(node1, node2, taxiway):
    neighbors = neighbor(node1, taxiway) # neighbors will have length <= 2 unless the taxiway is self-intersecting
    node_list = last_segment(node1, node1, node2, taxiway, neighbors[0])
    if node_list is None & len(neighbors) > 1:
        node_list = last_segment(node1, node1, node2, taxiway, neighbors[1])
    return node_list

# suppose we defined the neighbor() the nodes on a certain taxiway
def last_segment(pre_node, cur_node,aim_node, taxiway, neighbors):
    if neighbors == [] 
        return None
    else if head(heighbors) == pre_node:
        return last_segment(pre_node,cur_node, aim_node, taxiway, rest(neighbors)) #for
    else if head(neighbors) == aim_node: #(should be only one(if exists))
        # we're assuming that it exists, or it will be done in ==[]
        # for this case, it's done
        return head(neighbors)
    else: # if head(neighbors) != pre_node or aim_node
        return head(neighbors) :: last_segment(cur_node, head(neighbors), aim_node, taxiway, neighbor(head(neighbors)))
