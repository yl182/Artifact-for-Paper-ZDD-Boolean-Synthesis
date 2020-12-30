#ifdef __cplusplus
extern "C" {
#endif
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/custom.h>
#include <caml/memory.h>
#include <caml/fail.h>
#include <caml/callback.h>

#include "graph.h"
#include "graphops.h"
  
extern int tiebreaker, sign;
int slow_seed = 1;

static inline graph_t graph(value v)
{
  return *(graph_t*)Data_custom_val(v);
}

static void free_ml_graph(value v)
{
  free_graph(*(graph_t*)Data_custom_val(v));
}

int compare_graph(const value v1, const value v2)
{
  return (int)graph(v1) - (int)graph(v2);
}

struct custom_operations graph_ops = {
  "RGL/graph/OCaml",
  &free_ml_graph,
  &compare_graph,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default
};

static inline value alloc_res(graph_t g)
{
  value v = alloc_custom(&graph_ops, sizeof(graph_t), 0, 1);
  *(graph_t*)Data_custom_val(v) = g;
  return v;
}

value init_graph_rgl(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  int i;
  graph_t g = alloc_graph(GP_VERTEX_SET|GP_VERTEX_MAP);
  for (i=0;i<Int_val(v);i++) {
    connect_graph(g, i, i);
  }
  res = alloc_res(g);
  CAMLreturn(res);
}

value add_edge_graph_rgl(value v1, value v2, value v3)
{
  CAMLparam3(v1, v2, v3);
  CAMLlocal1(res);
  graph_t g = graph(v1);
  //  printf("%d %d\n", Int_val(v2), Int_val(v3));
  //  fflush(stdout);
  connect_graph(g, Int_val(v2), Int_val(v3));
  CAMLreturn(Val_unit);
}

value associate_graph(value v1, value v2, value v3)
{
  CAMLparam3(v1, v2, v3);
  CAMLlocal1(res);
  graph_t g = graph(v1);
  associate_vertex_graph(g, Int_val(v2), (void *)Int_val(v3));
  CAMLreturn(Val_unit);
}

value set_order_sign_rgl(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  sign = Int_val(v);
  res = Val_unit;
  CAMLreturn(res);
}

value set_order_tiebreaker_rgl(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  tiebreaker = Int_val(v);
  res = Val_unit;
  CAMLreturn(res);
}

value set_secondary_tiebreaker_rgl(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  tiebreaker_2 = Int_val(v);
  res = Val_unit;
  CAMLreturn(res);
}

value set_width_min_degree_rgl(value v)
{
  CAMLparam1(v);
  slow_seed = 0;
  CAMLreturn(Val_unit);
}

value lex_bfs_rgl(value v)
{
  CAMLparam1(v);
  CAMLlocal3(res, work, work2);
  graph_t g = graph(v);
  int size = num_vertices_graph(g);
  int i, width, minwidth, minwidthseed;
  int *elim = (int *)alloca(sizeof(int)*size);
  minwidth = size+1;
  minwidthseed = 0;
  if (slow_seed) {
    for (i=0;i<size;i++) {
      lexicographic_bfs_graph(g, i, elim);
      width = triangulate_graph(g, elim);
      if (width < minwidth) {
	minwidth = width;
	minwidthseed = i;
      }
    }
  } else {
    for (i=0;i<size;i++) {
      width = size_set(out_edges_graph(g, i));
      if (width < minwidth) {
	minwidth = width;
	minwidthseed = i;
      }
    }
  }
  lexicographic_bfs_graph(g, minwidthseed, elim);
  for (i=0;i<size;i++) {
    work = alloc_tuple(2);
    if (i==0)
      res = work;
    Field(work, 0) = Val_int(elim[i]);
    Field(work, 1) = Val_int(0);
    if (i!=0)
      modify(&Field(work2, 1), work);
    work2 = work;
  }
  CAMLreturn(res);
}

value lex_bfs_min_rgl(value v)
{
  CAMLparam1(v);
  CAMLlocal3(res, work, work2);
  graph_t g = graph(v);
  int size = num_vertices_graph(g);
  int i, width, minwidth, minwidthseed;
  int *elim = (int *)alloca(sizeof(int)*size);
  minwidth = size+1;
  minwidthseed = 0;
  if (slow_seed) {
    for (i=0;i<size;i++) {
      lexicographic_bfs_graph_min(g, i, elim);
      width = triangulate_graph(g, elim);
      if (width < minwidth) {
	minwidth = width;
	minwidthseed = i;
      }
    }
  } else {
    for (i=0;i<size;i++) {
      width = size_set(out_edges_graph(g, i));
      if (width < minwidth) {
	minwidth = width;
	minwidthseed = i;
      }
    }
  }
  lexicographic_bfs_graph_min(g, minwidthseed, elim);
  for (i=0;i<size;i++) {
    work = alloc_tuple(2);
    if (i==0)
      res = work;
    Field(work, 0) = Val_int(elim[i]);
    Field(work, 1) = Val_int(0);
    if (i!=0)
      modify(&Field(work2, 1), work);
    work2 = work;
  }
  CAMLreturn(res);
}

value mcs_rgl(value v)
{
  CAMLparam1(v);
  CAMLlocal3(res, work, work2);
  graph_t g = graph(v);
  int size = num_vertices_graph(g);
  int i, width, minwidth, minwidthseed;
  int *elim = (int *)alloca(sizeof(int)*size);
  minwidth = size+1;
  minwidthseed = 0;
  if (slow_seed) {
    for (i=0;i<size;i++) {
      mcs_graph(g, i, elim);
      width = triangulate_graph(g, elim);
      if (width < minwidth) {
	minwidth = width;
	minwidthseed = i;
      }
    }
  } else {
    for (i=0;i<size;i++) {
      width = size_set(out_edges_graph(g, i));
      if (width < minwidth) {
	minwidth = width;
	minwidthseed = i;
      }
    }
  }
  mcs_graph(g, minwidthseed, elim);
  for (i=0;i<size;i++) {
    work = alloc_tuple(2);
    if (i==0)
      res = work;
    Field(work, 0) = Val_int(elim[i]);
    Field(work, 1) = Val_int(0);
    if (i!=0)
      modify(&Field(work2, 1), work);
    work2 = work;
  }
  CAMLreturn(res);
}

value mcs_rgl_layered(value v)
{
  CAMLparam1(v);
  CAMLlocal3(res, work, work2);
  graph_t g = graph(v);
  int size = num_vertices_graph(g);
  int i;
  int *elim = (int *)alloca(sizeof(int)*size);
  mcs_graph_layered(g, elim);
  for (i=0;i<size;i++) {
    work = alloc_tuple(2);
    if (i==0)
      res = work;
    Field(work, 0) = Val_int(elim[i]);
    Field(work, 1) = Val_int(0);
    if (i!=0)
      modify(&Field(work2, 1), work);
    work2 = work;
  }
  CAMLreturn(res);
}

value min_induced_width_rgl(value v)
{
  CAMLparam1(v);
  CAMLlocal3(res, work, work2);
  graph_t g = graph(v);
  int size = num_vertices_graph(g);
  int i;
  int *elim = (int *)alloca(sizeof(int)*size);
  min_induced_width_graph(g, elim);
  for (i=0;i<size;i++) {
    work = alloc_tuple(2);
    if (i==0)
      res = work;
    Field(work, 0) = Val_int(elim[i]);
    Field(work, 1) = Val_int(0);
    if (i!=0)
      modify(&Field(work2, 1), work);
    work2 = work;
  }
  CAMLreturn(res);
}

value min_fill_rgl(value v)
{
  CAMLparam1(v);
  CAMLlocal3(res, work, work2);
  graph_t g = graph(v);
  int size = num_vertices_graph(g);
  int i;
  int *elim = (int *)alloca(sizeof(int)*size);
  min_fill_graph(g, elim);
  for (i=0;i<size;i++) {
    work = alloc_tuple(2);
    if (i==0)
      res = work;
    Field(work, 0) = Val_int(elim[i]);
    Field(work, 1) = Val_int(0);
    if (i!=0)
      modify(&Field(work2, 1), work);
    work2 = work;
  }
  CAMLreturn(res);
}

value new_alg_rgl(value v)
{
  CAMLparam1(v);
  CAMLlocal3(res, work, work2);
  graph_t g = graph(v);
  int size = num_vertices_graph(g);
  int i;
  int *elim = (int *)alloca(sizeof(int)*size);
  optimize_graph_mixed(g, elim);
  for (i=0;i<size;i++) {
    work = alloc_tuple(2);
    if (i==0)
      res = work;
    Field(work, 0) = Val_int(elim[i]);
    Field(work, 1) = Val_int(0);
    if (i!=0)
      modify(&Field(work2, 1), work);
    work2 = work;
  }
  CAMLreturn(res);
}

value tree_width_rgl(value v1, value v2)
{
  CAMLparam2(v1, v2);
  CAMLlocal1(res);
  graph_t g = graph(v1);
  int size = num_vertices_graph(g);
  int *elim = (int *)alloca(sizeof(int)*size);
  int i;
  for (i=0;i<size;i++) {
    elim[i] = Int_val(Field(v2, 0));
    v2 = Field(v2, 1);
  }
  res = Val_int(triangulate_graph(g, elim));
  CAMLreturn(res);
}

value triangulate_graph_rgl(value v1, value v2)
{
  CAMLparam2(v1, v2);
  CAMLlocal1(res);
  graph_t g = graph(v1);
  int size = num_vertices_graph(g);
  int *elim = (int *)alloca(sizeof(int)*size);
  int i;
  for (i=0;i<size;i++) {
    elim[i] = Int_val(Field(v2, 0))-1;
    v2 = Field(v2, 1);
  }
  res = Val_int(triangulate_graph_nodisconnect(g, elim));
  CAMLreturn(res);
}

value build_tree_decomposition_rgl(value v1, value v2)
{
  CAMLparam2(v1, v2);
  CAMLlocal1(res);
  graph_t g = graph(v1);
  int size = num_vertices_graph(g);
  int *elim = (int *)alloca(sizeof(int)*size);
  int i;
  for (i=0;i<size;i++) {
    elim[i] = Int_val(Field(v2, 0));
    v2 = Field(v2, 1);
  }
  res = alloc_res(build_tree_decomposition_graph(g, elim));
  CAMLreturn(res);  
}

value reroot_tree_decomposition_rgl(value v1, value v2)
{
  CAMLparam2(v1, v2);
  CAMLlocal3(res,work,work2);
  graph_t g = graph(v1);
  int size = num_vertices_graph(g);
  int *elim = (int *)alloca(sizeof(int)*size);
  int i;
  set_t root = alloc_set(0);
  while (v2 != Val_int(0)) {
    root = put_set(root, Int_val(Field(v2, 0)));
    v2 = Field(v2, 1);
  }
  reroot_tree_decomposition_graph(g, root, elim);
  res = alloc_tuple(2);
  work = res;
  for (i=0;i<size;i++) {
    Field(work, 0) = Val_int(elim[i]);
    if (i != size-1)
      Field(work, 1) = alloc_tuple(2);
    else
      Field(work, 1) = Val_int(0);
    work = Field(work, 1);
  }
  CAMLreturn(res);
  /*  res = alloc_tuple(2);
  work = res;
  for (i=0;i<size;i++) {
    Field(work, 0) = Val_int(elim[i]);
    if (i != size-1)
      Field(work, 1) = alloc_tuple(2);
    else
      Field(work, 1) = Val_int(0);
    work = Field(work, 1);
  }
  CAMLreturn(res);*/
}

value sift_graph_width_rgl(value v1, value v2, value v3)
{
  CAMLparam3(v1, v2, v3);
  CAMLlocal3(res, work, work2);
  graph_t g = graph(v1);
  int size = num_vertices_graph(g);
  int *elim = (int *)alloca(sizeof(int)*size);
  int i;
  set_t root = alloc_set(0);
  i = 0;
  for (i=0;i<size;i++) {
    elim[i] = Int_val(Field(v3, 0));
    v3 = Field(v3, 1);
  }
  sift_graph_width(g, Int_val(v2), elim);
  for (i=0;i<size;i++) {
    work = alloc_tuple(2);
    if (i==0)
      res = work;
    Field(work, 0) = Val_int(elim[i]);
    Field(work, 1) = Val_int(0);
    if (i!=0)
      modify(&Field(work2, 1), work);
    work2 = work;
  }
  CAMLreturn(res);
}

#ifdef __cplusplus
};
#endif
