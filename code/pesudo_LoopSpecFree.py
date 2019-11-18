
# suppose we defined the get_neighbors(node, taxiway) the nodes on a certain taxiway
# suppose we have a function last_node(node_list) to return the last element
# suppose we have a function drop_last(node_list) to return the list without last element
# suppose we have a function node_find(node, nodelist) to return whether a node is in a nodelist, it can acceptu for nil list

def get_last_segment(source_node, aim_node, taxiway):
    neighbors = neighbor(source_node, taxiway) # neighbors will have length <= 2 unless the taxiway is self-intersecting
    node_list = last_segment([source_node], source_node, aim_node, taxiway, [head(neighbors)]) #run the neighbor[0], imaging it exists
    if last_node(node_list) == source_node:     # it is what we want
        return drop_last(node_list)
    else:  
        return drop_last(last_segment([source_node], source_node, aim_node, taxiway, [last_node(neighbors)]))


def last_segment(pre_node_list, cur_node, aim_node, taxiway, neighbors):
    if node_find(head(neighbors), pre_node_list) == True:   # if loop
        return [] #just like it's empty, indicating that this path is end, and since not found, it will be dropped

    if neighbors == []: # if the path is end
        return []    
    else:
        if head(neighbors) == head(pre_node_list):  # if the backward
            return last_segment(pre_node_list, cur_node, aim_node, taxiway, tail(neighbors))
        else if head(neighbors) == aim_node:    # if end, the last_node(pre_node_list) is the checker
            return head(neighbors) :: last_node(pre_node_list)
        else:   #we need keep on
            return head(neighbors) :: last_segment( (cur_node::pre_node_list), head(neighbors), aim_node, taxiway, get_neighbors(head(neighbors))  )

#============================================================================
# it's similar to the previous function, only change is judge if ends
def get_intermediate_nodes(source_node, cur_taxi, next_taxi):
    neighbors = neighbor(source_node, cur_taxi) # neighbors will have length <= 2 unless the taxiway is self-intersecting
    node_list = intermediate_nodes([source_node], source_node, cur_taxi, next_taxi, [head(neighbors)])
    if last_node(node_list) == source_node:    
        return drop_last(node_list)
    else: 
        return drop_last(last_segment([source_node], source_node, aim_node, taxiway, [last_node(neighbors)]))


def intermediate_nodes(pre_node_list, cur_node, cur_taxi, next_taxi, neighbors):
    if node_find( head(neighbors), pre_node_list ) == True:
        return []

    if neighbors == []:
        return []
    else:
        if head(neighbors) == head(pre_node_list):
            return intermediate_nodes(pre_node_list, cur_node, cur_taxi, next_taxi, tail(neighbors))
        else if is_on_taxiway( head(neighbors), next_taxi ) == True:
            return head(neighbors) :: last_node(pre_node_list)
        else:
            return head(neighbors) :: intermediate_nodes( (cur_node::pre_node_list), head(neighbors), cur_taxi, next_taxi, get_neighbors(head(neighbors)) )

#============================================================================

def find_path(start_node, end_node, taxiway_names):
    path = [start_node]
    current_node = start_node
    for i in enumerate(taxiway_names): # do not allow out of bounds indexing
        path_segment = get_intermediate_nodes(current_node, taxiway_nodes[i], taxiway_nodes[i+1])
        if path_segment == null:
            fail
        path.append(path_segment)
        current_node = path[len(path) - 1]
    path_segment = get_last_segment(current_node, end_node, taxiway)
    if path_segment == null:
        fail
    path.append(path_segment)
    return path 