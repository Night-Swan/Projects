from graph import *
from graph_io import *

with open('test_cycles.grl') as f:
    L = load_graph(f, read_list=True)

GL = []
prev_colors = {} 
GV = []

for i in range(len(L[0])):
    GL.append(L[0][i])


for g in GL:
    for v in g:
        GV.append(v)

def col_ref(GV):

    global prev_colors
    for v in GV:
        prev_colors[v] = 0
    new_cols = prev_colors.copy()

    counter = True
    i = 0

    pod = {}

    lis_dis = []

    while counter:
        dict_ans = {}
        i += 1

        for v in GV:
            tr = {}
            for n in v.neighbours:
                tr[prev_colors[n]] = tr.get(prev_colors[n], 0) + 1

            if tr in dict_ans.values():
                col1 = next(key for key, value in dict_ans.items() if value == tr and key != prev_colors[v])
                new_cols[v] = col1
                dict_ans[col1] = tr
            else:
                l = max(new_cols.values())+1
                new_cols[v] = l
                dict_ans[l] = tr
            ism = []
            
        tvf = []
        for gi in range(len(GL)):
            ex = True
            tv1 = []
            tp1 = []
            for vf in GL[gi]:
                if prev_colors[vf] not in tp1:
                    tp1.append(prev_colors[vf])
                if new_cols[vf] not in tv1:
                    tv1.append(new_cols[vf])
            if len(tv1) == len(tp1):
                ex = False
                if gi not in pod.keys():
                    pod[gi] = i
            tvf.append(ex)
        
        if True not in tvf:
            counter = False
            

        prev_colors = new_cols.copy()


        
        ism = []
        for gri in range(len(GL)):
            for grv in range(len(GL)):
                isn = []
                if grv != gri:
                    vi = []
                    for vvi in GL[gri].vertices:
                        vi.append(prev_colors[vvi])
                    vv = []
                    for vvv in GL[grv].vertices:
                        vv.append(prev_colors[vvv])
                    if sorted(vi) == sorted(vv):
                        isn.append(grv)
                        isn.append(gri)
                ism.append(isn)

        if counter == False:
            #Remove empty lists
            ism2 = [suli for suli in ism if suli]

            #Remove duplicates
            uni = []

            lis = []
            for gii in range(len(GL)):
                lis.append(gii)
                        
        
            for subli in ism2:
                pair = sorted(subli)
                if pair not in uni:
                    uni.append(pair)
            merged_pairs = {}
            merged_elements = set()

            for pair in uni:
                sorted_pair = sorted(pair)
                if sorted_pair[0] not in merged_elements:
                    if sorted_pair[0] in merged_pairs:
                        merged_pairs[sorted_pair[0]] += sorted_pair[1:]
                    else:
                        merged_pairs[sorted_pair[0]] = sorted_pair
                    merged_elements.update(sorted_pair[1:])
            
            fin_mer = list(merged_pairs.values())
            fin_tup = [([vertex] + neighbors, pod[vertex]) for sublist in fin_mer for vertex, *neighbors in [sublist]]
            res = fin_tup+ [([item], pod[item]) for item in lis if item not in [item for sublist in uni for item in sublist]]

            for fri in range(len(GL)):
                if len(GL[fri].vertices) == 1:
                    lis_dis.append(fri)


            fin_res = [(*item, item[0][0] in lis_dis) for item in res]
            for pair in fin_mer:
                val1 = pair[0]
                sum_values = pod[val1]
    
                if val1 in lis_dis:
                    print(f"{pair} {sum_values} discrete")
                else:
                    print(f"{pair} {sum_values}")

            print(f"The final answer is {fin_res}")
        
        for gri in range(len(GL)):
            ver_li = []
            for vr in GL[gri].vertices:
                ver_li.append(new_cols[vr])
            vnum = len(GL[gri].vertices)
            ver_se = set(ver_li)
            if vnum == len(ver_se):
                lis_dis.append(gri)
        
        print(f"Iterations is {i}")
    print(f"Final iterations is {i}")

col_ref(GV)


