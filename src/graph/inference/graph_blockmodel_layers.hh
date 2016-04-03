// graph-tool -- a general graph modification and manipulation thingy
//
// Copyright (C) 2006-2016 Tiago de Paula Peixoto <tiago@skewed.de>
//
// This program is free software; you can redistribute it and/or
// modify it under the terms of the GNU General Public License
// as published by the Free Software Foundation; either version 3
// of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program. If not, see <http://www.gnu.org/licenses/>.

#ifndef GRAPH_BLOCKMODEL_LAYERS_HH
#define GRAPH_BLOCKMODEL_LAYERS_HH

#include "config.h"

#include <vector>

#include "graph_state.hh"
#include "graph_blockmodel_layers_util.hh"

namespace graph_tool
{
using namespace boost;
using namespace std;

typedef eprop_map_t<int32_t>::type emap_t;
typedef vprop_map_t<std::vector<int32_t>>::type vcvmap_t;

typedef gt_hash_map<size_t, size_t> bmap_t;
typedef std::vector<bmap_t> vbmap_t;

#define LAYERED_BLOCK_STATE_params                                             \
    ((__class__,&, mpl::vector<python::object>, 1))                            \
    ((layer_states,, python::object, 0))                                       \
    ((ec,, emap_t, 0))                                                         \
    ((vc,, vcvmap_t, 0))                                                       \
    ((vmap,, vcvmap_t, 0))                                                     \
    ((block_map, &, vbmap_t&, 0))                                              \
    ((master,, bool, 0))

template <class BaseState>
struct Layers
{
    GEN_STATE_BASE(LayeredBlockStateBase, LAYERED_BLOCK_STATE_params)

    template <class... Ts>
    class LayeredBlockState
        : public LayeredBlockStateBase<Ts...>,
          public BaseState
    {
    public:
        GET_PARAMS_USING(LayeredBlockStateBase<Ts...>,
                         LAYERED_BLOCK_STATE_params)
        GET_PARAMS_TYPEDEF(Ts, LAYERED_BLOCK_STATE_params)

        GET_PARAMS_USING(BaseState, BASE_STATE_params)
        using BaseState::_bg;
        using BaseState::_m_entries;
        using BaseState::_emat;
        using BaseState::_partition_stats;
        using BaseState::is_partition_stats_enabled;

        typedef vprop_map_t<int32_t>::type block_rmap_t;

        class LayerState
            : public BaseState
        {
        public:
            LayerState(const BaseState& base_state, bmap_t& block_map,
                       block_rmap_t block_rmap, vector<size_t>& free_blocks)
                : BaseState(base_state),
                  _block_map(block_map),
                  _block_rmap(block_rmap),
                  _free_blocks(free_blocks),
                  _E(0)
            {
                for (auto e : edges_range(BaseState::_g))
                    _E += BaseState::_eweight[e];
            }

            bmap_t& _block_map;
            block_rmap_t _block_rmap;
            vector<size_t>& _free_blocks;
            size_t _E;

            size_t get_block_map(size_t r, bool put_new=true)
            {
                size_t r_u;
                auto iter = _block_map.find(r);
                if (iter == _block_map.end())
                {
                    if (_free_blocks.empty())
                    {
                        r_u = _block_map.size();
                    }
                    else
                    {
                        r_u = _free_blocks.back();
                        if (put_new)
                            _free_blocks.pop_back();
                    }
                    if (put_new)
                    {
                        _block_map[r] = r_u;
                        _block_rmap[r_u] = r;
                    }
                }
                else
                {
                    r_u = iter->second;
                }
                assert(r_u < num_vertices(_bg));
                return r_u;
            }

            void remove_block_map(size_t r, bool free_block=true)
            {
                auto iter = _block_map.find(r);
                if (free_block)
                    _free_blocks.push_back(iter->second);
                _block_map.erase(iter);
            }

            void put_block_map(size_t r, size_t r_u)
            {
                _block_map[r] = r_u;
            }

            bool has_block_map(size_t r)
            {
                return _block_map.find(r) != _block_map.end();
            }
        };

        template <class... ATs,
                  typename std::enable_if_t<sizeof...(ATs) == sizeof...(Ts)>* = nullptr>
        LayeredBlockState(const BaseState& base_state, ATs&&... args)
            : LayeredBlockStateBase<Ts...>(std::forward<ATs>(args)...),
              BaseState(base_state), _total_B(0),
              _is_partition_stats_enabled(false)
        {
            for (int i = 0; i < python::len(_layer_states); ++i)
            {
                auto ostate = _layer_states[i];
                BaseState& state = python::extract<BaseState&>(ostate.attr("_state"));
                boost::python::object temp = ostate.attr("block_rmap").attr("_get_any")();
                boost::any& a = python::extract<boost::any&>(temp);
                block_rmap_t block_rmap = boost::any_cast<block_rmap_t>(a);
                std::vector<size_t>& free_blocks =
                    python::extract<std::vector<size_t>&>(ostate.attr("free_blocks"));
                bmap_t& block_map = _block_map[i];
                _layers.emplace_back(state, block_map, block_rmap, free_blocks);
            }
            for (auto r : vertices_range(BaseState::_bg))
                if (BaseState::_wr[r] > 0)
                    _total_B++;
        }

        std::vector<LayerState> _layers;
        size_t _total_B;
        bool _is_partition_stats_enabled;

        //TODO: remove_vertex and add_vertex, etc.

        void move_vertex(size_t v, size_t s)
        {
            if (BaseState::_vweight[v] == 0)
            {
                _b[v] = s;
                return;
            }

            size_t r = _b[v];

            if (r == s)
                return;

            if (_wr[s] == 0)
                _total_B++;

            BaseState::move_vertex(v, s);

            if (_wr[r] == 0)
                _total_B--;

            auto& ls = _vc[v];
            auto& vs = _vmap[v];
            for (size_t j = 0; j < ls.size(); ++j)
            {
                int l = ls[j];
                size_t u = vs[j];

                auto& state = _layers[l];
                size_t r_u = state._b[u];

                assert(r_u < num_vertices(state._bg));

                if (state.virtual_remove_size(u) == 0 && !state.has_block_map(s))
                {
                    state.remove_block_map(r, false);
                    state.put_block_map(s, r_u);
                }
                else
                {
                    size_t s_u = state.get_block_map(s);
                    state.move_vertex(u, s_u);
                    if (state._wr[r_u] == 0)
                        state.remove_block_map(r);
                }
            }
        }

        template <class MEntries>
        double virtual_move(size_t v, size_t s, bool dense, bool multigraph,
                            bool partition_dl, bool deg_dl, bool edges_dl,
                            MEntries& m_entries)
        {
            size_t r = _b[v];

            if (s == r)
                return 0;

            double dS = 0;

            if (_master)
            {
                dS += BaseState::virtual_move(v, s, dense, multigraph,
                                              partition_dl, deg_dl, false,
                                              m_entries);
                dS -= virtual_move_covariate(v, s, *this, m_entries, false);
            }
            else
            {
                if (partition_dl)
                {
                    enable_partition_stats();
                    dS += BaseState::get_delta_dl(v, s);
                }
            }

            if (edges_dl)
                dS += get_delta_edges_dl(v, s);

            auto& ls = _vc[v];
            auto& vs = _vmap[v];
            for (size_t j = 0; j < ls.size(); ++j)
            {
                size_t l = ls[j];
                size_t u = vs[j];

                auto& state = _layers[l];

                size_t s_u = state.get_block_map(s, false);

                if (_master)
                    dS += virtual_move_covariate(u, s_u, state, m_entries,
                                                 true);
                else
                    dS += state.virtual_move(u, s_u, dense, multigraph, false,
                                             deg_dl, false, m_entries);

            }
            return dS;
        }

        double virtual_move(size_t v, size_t s, bool dense, bool multigraph,
                            bool partition_dl, bool deg_dl, bool edges_dl)
        {
            return virtual_move(v, s, dense, multigraph, partition_dl, deg_dl,
                                edges_dl, _m_entries);
        }

        double get_delta_edges_dl(size_t v, size_t s)
        {
            if (BaseState::_vweight[v] == 0)
                return 0;
            int dB = 0;
            if (BaseState::virtual_remove_size(v) == 0)
                --dB;
            if (_wr[s] == 0)
                ++dB;
            double S_a = 0, S_b = 0;
            if (dB != 0)
            {
                auto get_x = [](size_t B)
                    {
                        if (is_directed::apply<typename BaseState::g_t>::type::value)
                            return B * B;
                        else
                            return (B * (B + 1)) / 2;
                    };

                for (auto& state : _layers)
                {
                    S_b += lbinom(get_x(_total_B) + state._E - 1, state._E);
                    S_a += lbinom(get_x(_total_B + dB) + state._E - 1, state._E);
                }
            }
            return S_a - S_b;
        }

        void merge_vertices(size_t u, size_t v)
        {
            std::set<size_t> ls;
            gt_hash_map<size_t, size_t> ls_u, ls_v;
            for (size_t i = 0; i < _vc[u].size(); ++i)
            {
                size_t l = _vc[u][i];
                ls_u[l] = _vmap[u][i];
                ls.insert(l);
            }

            for (size_t i = 0; i < _vc[v].size(); ++i)
            {
                size_t l = _vc[v][i];
                ls_v[l] = _vmap[v][i];
                ls.insert(l);
            }

            _vc[u].clear();
            _vmap[u].clear();
            _vc[v].clear();
            _vmap[v].clear();

            for (auto l : ls)
            {
                auto iter_u = ls_u.find(l);
                auto iter_v = ls_v.find(l);

                size_t uu = (iter_u != ls_u.end()) ? iter_u->second : iter_v->second;
                size_t vv = (iter_v != ls_v.end()) ? iter_v->second : iter_u->second;

                _layers[l].merge_vertices(uu, vv);

                _vc[v].push_back(l);
                _vmap[v].push_back(vv);
            }

            auto ec = _ec.get_checked();
            BaseState::merge_vertices(u, v, ec);
        }

        double entropy(bool dense, bool multigraph, bool deg_entropy)
        {
            double S = 0;
            if (_master)
            {
                S += BaseState::entropy(dense, multigraph, deg_entropy);
                S -= covariate_entropy(_bg, _mrs);
                if (multigraph)
                    S -= BaseState::get_parallel_entropy();
                for (auto& state : _layers)
                {
                    S += covariate_entropy(state._bg, state._mrs);
                    if (multigraph)
                        S += state.get_parallel_entropy();
                }
            }
            else
            {
                for (auto& state : _layers)
                    S += state.entropy(dense, multigraph, deg_entropy);
            }
            return S;
        }

        double get_deg_dl(bool ent, bool dl_alt, bool xi_fast)
        {
            if (_master)
            {
                return BaseState::get_deg_dl(ent, dl_alt, xi_fast);
            }
            else
            {
                double S = 0;
                for (auto& state : _layers)
                    S += state.get_deg_dl(ent, dl_alt, xi_fast);
                return S;
            }
        }

        void enable_partition_stats()
        {
            if (!_is_partition_stats_enabled)
            {
                BaseState::enable_partition_stats();
                for (auto& state : _layers)
                    state.enable_partition_stats();
                _is_partition_stats_enabled = true;
            }
        }

        void disable_partition_stats()
        {
            BaseState::disable_partition_stats();
            for (auto& state : _layers)
                state.disable_partition_stats();
            _is_partition_stats_enabled = false;
        }

        void init_mcmc(double c, double dl)
        {
            BaseState::init_mcmc(c, dl);
            for (auto& state : _layers)
                state.init_mcmc(numeric_limits<double>::infinity(), dl);
        }
    };
};

} // graph_tool namespace

#endif //GRAPH_BLOCKMODEL_LAYERS_HH