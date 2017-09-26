// graph-tool -- a general graph modification and manipulation thingy
//
// Copyright (C) 2006-2017 Tiago de Paula Peixoto <tiago@skewed.de>
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

#ifndef GRAPH_BLOCKMODEL_HH
#define GRAPH_BLOCKMODEL_HH

#include "config.h"

#include <vector>

#include "../support/graph_state.hh"
#include "graph_blockmodel_util.hh"

#include "openmp_lock.hh"

namespace graph_tool
{
using namespace boost;
using namespace std;

typedef vprop_map_t<int32_t>::type vmap_t;
typedef eprop_map_t<int32_t>::type emap_t;
typedef UnityPropertyMap<int,GraphInterface::vertex_t> vcmap_t;
typedef UnityPropertyMap<int,GraphInterface::edge_t> ecmap_t;

template <class PMap>
auto uncheck(boost::any& amap, PMap*)
{
    return any_cast<typename PMap::checked_t&>(amap).get_unchecked();
}

template <class T, class V>
auto& uncheck(boost::any& amap, UnityPropertyMap<T,V>*)
{
    return any_cast<UnityPropertyMap<T,V>&>(amap);
}

inline simple_degs_t uncheck(boost::any& amap, simple_degs_t*)
{
    return any_cast<simple_degs_t>(amap);
}

typedef mpl::vector2<std::true_type, std::false_type> bool_tr;
typedef mpl::vector2<vcmap_t, vmap_t> vweight_tr;
typedef mpl::vector2<ecmap_t, emap_t> eweight_tr;

#define BLOCK_STATE_params                                                     \
    ((g, &, all_graph_views, 1))                                               \
    ((is_weighted,, bool_tr, 1))                                               \
    ((use_hash,, bool_tr, 1))                                                  \
    ((_abg, &, boost::any&, 0))                                                \
    ((_aeweight, &, boost::any&, 0))                                           \
    ((_avweight, &, boost::any&, 0))                                           \
    ((_adegs, &, boost::any&, 0))                                              \
    ((mrs,, emap_t, 0))                                                        \
    ((mrp,, vmap_t, 0))                                                        \
    ((mrm,, vmap_t, 0))                                                        \
    ((wr,, vmap_t, 0))                                                         \
    ((b,, vmap_t, 0))                                                          \
    ((empty_blocks, & ,std::vector<size_t>&, 0))                               \
    ((empty_pos,, vmap_t, 0))                                                  \
    ((candidate_blocks, &, std::vector<size_t>&, 0))                           \
    ((candidate_pos,, vmap_t, 0))                                              \
    ((bclabel,, vmap_t, 0))                                                    \
    ((pclabel,, vmap_t, 0))                                                    \
    ((merge_map,, vmap_t, 0))                                                  \
    ((deg_corr,, bool, 0))                                                     \
    ((rec_types,, std::vector<int32_t>, 0))                                    \
    ((rec,, std::vector<eprop_map_t<double>::type>, 0))                        \
    ((drec,, std::vector<eprop_map_t<double>::type>, 0))                       \
    ((brec,, std::vector<eprop_map_t<double>::type>, 0))                       \
    ((bdrec,, std::vector<eprop_map_t<double>::type>, 0))                      \
    ((brecsum,, vprop_map_t<double>::type, 0))                                 \
    ((wparams, &, std::vector<std::vector<double>>&, 0))                       \
    ((recdx, &, std::vector<double>&, 0))                                      \
    ((Lrecdx, &, std::vector<double>&, 0))                                     \
    ((epsilon, &, std::vector<double>&, 0))                                    \
    ((ignore_degrees,, typename vprop_map_t<uint8_t>::type, 0))                \
    ((bignore_degrees,, typename vprop_map_t<uint8_t>::type, 0))               \
    ((allow_empty,, bool, 0))

GEN_STATE_BASE(BlockStateBase, BLOCK_STATE_params)

template <class... Ts>
class BlockState
    : public BlockStateBase<Ts...>, public BlockStateVirtualBase
{
public:
    GET_PARAMS_USING(BlockStateBase<Ts...>, BLOCK_STATE_params)
    GET_PARAMS_TYPEDEF(Ts, BLOCK_STATE_params)

    template <class RNG, class... ATs,
              typename std::enable_if_t<sizeof...(ATs) == sizeof...(Ts)>* = nullptr>
    BlockState(RNG& rng, ATs&&... args)
        : BlockStateBase<Ts...>(std::forward<ATs>(args)...),
          _bg(boost::any_cast<std::reference_wrapper<bg_t>>(__abg)),
          _c_mrs(_mrs.get_checked()),
          _vweight(uncheck(__avweight, typename std::add_pointer<vweight_t>::type())),
          _eweight(uncheck(__aeweight, typename std::add_pointer<eweight_t>::type())),
          _degs(uncheck(__adegs, typename std::add_pointer<degs_t>::type())),
          _emat(_bg, rng),
          _neighbor_sampler(_g, _eweight),
          _m_entries(num_vertices(_bg))
    {
        _empty_blocks.clear();
        _candidate_blocks.clear();
        _candidate_blocks.push_back(null_group);
        for (auto r : vertices_range(_bg))
        {
            if (_wr[r] == 0)
                add_element(_empty_blocks, _empty_pos, r);
            else
                add_element(_candidate_blocks, _candidate_pos, r);
        }
        for (auto& p : _rec)
            _c_rec.push_back(p.get_checked());
        for (auto& p : _drec)
            _c_drec.push_back(p.get_checked());
        for (auto& p : _brec)
        {
            _c_brec.push_back(p.get_checked());
            double x = 0;
            for (auto me : edges_range(_bg))
                x += p[me];
            _recsum.push_back(x);
        }
        for (auto& p : _bdrec)
            _c_bdrec.push_back(p.get_checked());

        if (!_rec_types.empty())
        {
            _recx2.resize(_rec_types.size());
            _recdx.resize(_rec_types.size());
            for (auto me : edges_range(_bg))
            {
                if (_brec[0][me] > 0)
                {
                    _B_E++;
                    for (size_t i = 0; i < _rec_types.size(); ++i)
                    {
                        if (_rec_types[i] == weight_type::REAL_NORMAL)
                        {
                            _recx2[i] += std::pow(_brec[i][me], 2);
                            if (_brec[0][me] > 1)
                                _recdx[i] += \
                                    (_bdrec[i][me] -
                                     std::pow(_brec[i][me], 2) / _brec[0][me]);
                        }
                    }
                }
                if (_brec[0][me] > 1)
                    _B_E_D++;
            }
        }

        _rt = weight_type::NONE;
        for (auto rt : _rec_types)
        {
            _rt = rt;
            if (rt == weight_type::REAL_NORMAL)
                break;
        }
        _dBdx.resize(_rec_types.size());
    }

    BlockState(const BlockState& other)
        : BlockStateBase<Ts...>(static_cast<const BlockStateBase<Ts...>&>(other)),
          _bg(boost::any_cast<std::reference_wrapper<bg_t>>(__abg)),
          _c_mrs(_mrs.get_checked()),
          _c_rec(other._c_rec),
          _c_drec(other._c_drec),
          _c_brec(other._c_brec),
          _c_bdrec(other._c_bdrec),
          _recsum(other._recsum),
          _recx2(other._recx2),
          _dBdx(other._dBdx),
          _B_E(other._B_E),
          _B_E_D(other._B_E_D),
          _rt(other._rt),
          _vweight(uncheck(__avweight, typename std::add_pointer<vweight_t>::type())),
          _eweight(uncheck(__aeweight, typename std::add_pointer<eweight_t>::type())),
          _degs(uncheck(__adegs, typename std::add_pointer<degs_t>::type())),
          _emat(other._emat),
          _egroups_enabled(other._egroups_enabled),
          _neighbor_sampler(other._neighbor_sampler),
          _m_entries(num_vertices(_bg))
    {
        if (other.is_partition_stats_enabled())
            enable_partition_stats();
    }

    // =========================================================================
    // State modification
    // =========================================================================

    template <class MEntries, class EFilt>
    void get_move_entries(size_t v, size_t r, size_t nr, MEntries& m_entries,
                          EFilt&& efilt)
    {
        auto mv_entries = [&](auto&&... args)
            {
                move_entries(v, r, nr, _b, _g, _eweight, num_vertices(_bg),
                             m_entries, std::forward<EFilt>(efilt),
                             is_loop_nop(),
                             std::forward<decltype(args)>(args)...);
            };

        if (_rt == weight_type::NONE)
        {
            mv_entries();
        }
        else
        {
            if (_rt == weight_type::REAL_NORMAL)
                mv_entries(_rec, _drec);
            else
                mv_entries(_rec);
        }
    }

    template <class MEntries>
    void get_move_entries(size_t v, size_t r, size_t nr, MEntries& m_entries)
    {
        get_move_entries(v, r, nr, m_entries, [](auto) {return false;});
    }


    template <bool Add, class EFilt>
    void modify_vertex(size_t v, size_t r, EFilt&& efilt)
    {
        if (Add)
            get_move_entries(v, null_group, r, _m_entries,
                             std::forward<EFilt>(efilt));
        else
            get_move_entries(v, r, null_group, _m_entries,
                             std::forward<EFilt>(efilt));

        auto eops = [&](auto&& mid_op, auto&& end_op)
            {
                entries_op(_m_entries, _emat,
                           [&](auto r, auto s, auto& me, auto& delta)
                           {
                               if (get<0>(delta) == 0) // can happen with
                                   return;             // zero-weight edges

                               if (Add && me == _emat.get_null_edge())
                               {
                                   me = boost::add_edge(r, s, this->_bg).first;
                                   this->_emat.put_me(r, s, me);
                                   this->_c_mrs[me] = 0;
                                   for (size_t i = 0; i < this->_rec_types.size(); ++i)
                                   {
                                       this->_c_brec[i][me] = 0;
                                       this->_c_bdrec[i][me] = 0;
                                   }
                               }

                               mid_op(me, delta);

                               this->_mrs[me] += get<0>(delta);
                               this->_mrp[r] += get<0>(delta);
                               this->_mrm[s] += get<0>(delta);

                               assert(this->_mrs[me] >= 0);
                               assert(this->_mrp[r] >= 0);
                               assert(this->_mrm[s] >= 0);

                               end_op(me, delta);
                           });
                   };

        if (_rec_types.empty())
        {
            eops([](auto&, auto&){}, [](auto&, auto&){});
        }
        else
        {
            auto end_op = [&](auto& me, auto& delta)
                {
                    for (size_t i = 0; i < this->_rec_types.size(); ++i)
                    {
                        switch (this->_rec_types[i])
                        {
                        case weight_type::REAL_NORMAL: // signed weights
                            this->_bdrec[i][me] += get<2>(delta)[i];
                            [[gnu::fallthrough]];
                        default:
                            this->_brec[i][me] += get<1>(delta)[i];
                        }
                    }
                };

            auto mid_op_BE =
                [&](auto& me, auto&& delta)
                {
                    auto mrs = this->_brec[0][me];
                    if (Add && mrs == 0 && mrs + get<1>(delta)[0] > 0)
                    {
                        _B_E++;
                        if (_coupled_state != nullptr)
                            _coupled_state->add_edge(me);
                    }

                    if (!Add && mrs > 0 && mrs + get<1>(delta)[0] == 0)
                    {
                        _B_E--;
                        if (_coupled_state != nullptr)
                            _coupled_state->remove_edge(me);
                    }
                };

            if (_rt != weight_type::REAL_NORMAL)
            {
                eops(mid_op_BE, end_op);
            }
            else
            {
                auto mid_op =
                    [&](auto& me, auto&& delta)
                    {
                        auto& mrs = this->_brec[0][me];
                        mid_op_BE(me, delta);

                        auto n_mrs = mrs + get<1>(delta)[0];

                        if (n_mrs > 1)
                        {

                            if (Add && mrs < 2)
                            {
                                if (_B_E_D == 0 && this->_Lrecdx[0] >= 0)
                                    this->_Lrecdx[0] += 1;
                                _B_E_D++;
                            }

                            for (size_t i = 0; i < this->_rec_types.size(); ++i)
                            {
                                if (this->_rec_types[i] != weight_type::REAL_NORMAL)
                                    continue;
                                auto dx = \
                                    (this->_bdrec[i][me] + get<2>(delta)[i]
                                     - (std::pow((this->_brec[i][me] +
                                                  get<1>(delta)[i]), 2) / n_mrs));
                                this->_recdx[i] += dx;
                            }
                        }

                        if (mrs > 1)
                        {
                            if (!Add && n_mrs < 2)
                            {
                                _B_E_D--;
                                if (_B_E_D == 0 && this->_Lrecdx[0] >= 0)
                                    this->_Lrecdx[0] -= 1;
                            }

                            for (size_t i = 0; i < this->_rec_types.size(); ++i)
                            {
                                if (this->_rec_types[i] != weight_type::REAL_NORMAL)
                                    continue;
                                auto dx = (this->_bdrec[i][me] -
                                           std::pow(this->_brec[i][me], 2) / mrs);
                                this->_recdx[i] -= dx;
                            }
                        }

                        for (size_t i = 0; i < this->_rec_types.size(); ++i)
                        {
                            if (this->_rec_types[i] == weight_type::REAL_NORMAL)
                            {
                                _recx2[i] -= std::pow(this->_brec[i][me], 2);
                                _recx2[i] += std::pow(this->_brec[i][me] +
                                                      get<1>(delta)[i], 2);
                            }
                        }

                    };

                auto coupled_end_op = [&](auto& me, auto& delta)
                    {
                        end_op(me, delta);
                        if (_coupled_state != nullptr)
                            _coupled_state->update_edge(me, get<1>(delta));
                    };

                if (_Lrecdx[0] >= 0)
                {
                    for (size_t i = 0; i < _rec_types.size(); ++i)
                        _Lrecdx[i+1] -= _recdx[i] * _B_E_D;
                }

                eops(mid_op, coupled_end_op);

                if (_Lrecdx[0] >= 0)
                {
                    for (size_t i = 0; i < _rec_types.size(); ++i)
                        _Lrecdx[i+1] += _recdx[i] * _B_E_D;
                }
            }
        }

        if (!_rec_types.empty() &&
            _rec_types[1] == weight_type::DELTA_T) // waiting times
        {
            if (_ignore_degrees[v] > 0)
            {
                auto dt = out_degreeS()(v, _g, _rec[1]);
                if (Add)
                    _brecsum[r] += dt;
                else
                    _brecsum[r] -= dt;
            }
        }

        if (Add)
            BlockState::add_partition_node(v, r);
        else
            BlockState::remove_partition_node(v, r);
    }

    void add_edge(const GraphInterface::edge_t& e)
    {
        if (_rec_types.empty())
            return;
        auto crec = _rec[0].get_checked();
        crec[e] = 1;
        for (size_t i = 1; i < _rec_types.size(); ++i)
        {
            auto drec = _drec[i].get_checked();
            drec[e] = 0;
        }
        size_t r = _b[source(e, _g)];
        size_t s = _b[target(e, _g)];
        auto& me = _emat.get_me(r, s);
        assert(me != _emat.get_null_edge());
        _brec[0][me] += 1;

        if (_brec[0][me] == 1)
            _B_E++;

        size_t old_B_E_D = _B_E_D;
        if (_brec[0][me] == 2)
        {
            if (_B_E_D == 0 && _Lrecdx[0] >= 0)
                _Lrecdx[0] += 1;
            _B_E_D++;
        }

        if (_rt == weight_type::REAL_NORMAL && _brec[0][me] > 1)
        {
            for (size_t i = 0; i < _rec_types.size(); ++i)
            {
                if (_rec_types[i] != weight_type::REAL_NORMAL)
                    continue;

                if (_Lrecdx[0] >= 0)
                    _Lrecdx[i+1] -= _recdx[i] * old_B_E_D;

                auto dx = (_bdrec[i][me] -
                           std::pow(_brec[i][me], 2) / _brec[0][me]);
                _recdx[i] += dx;
                if (_brec[0][me] > 2)
                {
                    dx = (_bdrec[i][me] -
                          std::pow(_brec[i][me], 2) / (_brec[0][me] - 1));
                    _recdx[i] -= dx;
                }

                if (_Lrecdx[0] >= 0)
                    _Lrecdx[i+1] += _recdx[i] * _B_E_D;
            }
        }
    }

    void remove_edge(const GraphInterface::edge_t& e)
    {
        if (_rec_types.empty())
            return;

        size_t r = _b[source(e, _g)];
        size_t s = _b[target(e, _g)];
        auto& me = _emat.get_me(r, s);
        _brec[0][me] -= 1;
        _rec[0][e] = 0;

        if (_brec[0][me] == 0)
            _B_E--;

        size_t old_B_E_D = _B_E_D;
        if (_brec[0][me] == 1)
        {
            _B_E_D--;
            if (_B_E_D == 0 && _Lrecdx[0] >= 0)
                _Lrecdx[0] -= 1;
        }

        if (_rt == weight_type::REAL_NORMAL && _brec[0][me] > 0)
        {
            for (size_t i = 0; i < _rec_types.size(); ++i)
            {
                if (_rec_types[i] != weight_type::REAL_NORMAL)
                    continue;
                if (_Lrecdx[0] >= 0)
                    _Lrecdx[i+1] -= _recdx[i] * old_B_E_D;
                auto dx = (_bdrec[i][me] -
                           std::pow(_brec[i][me], 2) / (_brec[0][me] + 1));
                _recdx[i] -= dx;
                if (_brec[0][me] > 1)
                {
                    dx = (_bdrec[i][me] -
                          std::pow(_brec[i][me], 2) / _brec[0][me]);
                    _recdx[i] += dx;
                }
                if (_Lrecdx[0] >= 0)
                    _Lrecdx[i+1] += _recdx[i] * _B_E_D;
            }
        }
    }

    void update_edge(const GraphInterface::edge_t& e,
                     const std::vector<double>& delta)
    {
        if (_rec_types.empty())
            return;

        size_t r = _b[source(e, _g)];
        size_t s = _b[target(e, _g)];
        auto& me = _emat.get_me(r, s);
        auto ers = _brec[0][me];
        for (size_t i = 0; i < _rec_types.size(); ++i)
        {
            if (_rec_types[i] != weight_type::REAL_NORMAL)
                continue;

            auto rec = _c_rec[i][e];
            auto d = (std::pow(rec, 2) -
                      std::pow(rec - delta[i], 2));
            _c_drec[i][e] += d;
            _bdrec[i][me] += d;
            if (ers > 1)
            {
                _recdx[i] += d;
                if (_Lrecdx[0] >= 0)
                    _Lrecdx[i+1] += d * _B_E_D;
            }
        }
    }

    void remove_partition_node(size_t v, size_t r)
    {
        assert(size_t(_b[v]) == r);

        _wr[r] -= _vweight[v];

        if (!_egroups.empty() && _egroups_enabled)
            _egroups.remove_vertex(v, _b, _g);

        if (is_partition_stats_enabled())
            get_partition_stats(v).remove_vertex(v, r, _deg_corr, _g,
                                                 _vweight, _eweight,
                                                 _degs);

        if (_vweight[v] > 0 && _wr[r] == 0)
        {
            remove_element(_candidate_blocks, _candidate_pos, r);
            add_element(_empty_blocks, _empty_pos, r);
        }
    }

    void add_partition_node(size_t v, size_t r)
    {
        _b[v] = r;

        _wr[r] += _vweight[v];

        if (!_egroups.empty() && _egroups_enabled)
            _egroups.add_vertex(v, _b, _eweight, _g);

        if (is_partition_stats_enabled())
            get_partition_stats(v).add_vertex(v, r, _deg_corr, _g, _vweight,
                                              _eweight, _degs);

        if (_vweight[v] > 0 && _wr[r] == _vweight[v])
        {
            remove_element(_empty_blocks, _empty_pos, r);
            add_element(_candidate_blocks, _candidate_pos, r);
        }
    }

    template <class EFilt>
    void remove_vertex(size_t v, size_t r, EFilt&& efilt)
    {
        modify_vertex<false>(v, r, std::forward<EFilt>(efilt));
    }

    void remove_vertex(size_t v, size_t r)
    {
        remove_vertex(v, r,  [](auto&) { return false; });
    }

    void remove_vertex(size_t v)
    {
        size_t r = _b[v];
        remove_vertex(v, r);
    }

    template <class Vlist>
    void remove_vertices(Vlist& vs)
    {
        typedef typename graph_traits<g_t>::vertex_descriptor vertex_t;
        typedef typename graph_traits<g_t>::edge_descriptor edges_t;

        gt_hash_set<vertex_t> vset(vs.begin(), vs.end());

        gt_hash_set<edges_t> eset;
        for (auto v : vset)
        {
            for (auto e : all_edges_range(v, _g))
            {
                auto u = (source(e, _g) == v) ? target(e, _g) : source(e, _g);
                if (vset.find(u) != vset.end())
                    eset.insert(e);
            }
        }

        for (auto v : vset)
            remove_vertex(v, _b[v],
                          [&](auto& e) { return eset.find(e) != eset.end(); });

        for (auto& e : eset)
        {
            vertex_t v = source(e, _g);
            vertex_t u = target(e, _g);
            vertex_t r = _b[v];
            vertex_t s = _b[u];

            auto me = _emat.get_me(r, s);

            auto ew = _eweight[e];
            _mrs[me] -= ew;

            assert(_mrs[me] >= 0);

            _mrp[r] -= ew;
            _mrm[s] -= ew;

            for (size_t i = 0; i < _rec_types.size(); ++i)
            {
                switch (_rec_types[i])
                {
                case weight_type::REAL_NORMAL: // signed weights
                    _bdrec[i][me] -= _drec[i][e];
                    [[gnu::fallthrough]];
                default:
                    _brec[i][me] -= _rec[i][e];
                }
            }

            if (_mrs[me] == 0)
                _emat.remove_me(me, _bg);
        }
    }

    void remove_vertices(python::object ovs)
    {
        multi_array_ref<uint64_t, 1> vs = get_array<uint64_t, 1>(ovs);
        remove_vertices(vs);
    }

    template <class EFilt>
    void add_vertex(size_t v, size_t r, EFilt&& efilt)
    {
        modify_vertex<true>(v, r, std::forward<EFilt>(efilt));
    }

    void add_vertex(size_t v, size_t r)
    {
        add_vertex(v, r, [](auto&){ return false; });
    }

    template <class Vlist, class Blist>
    void add_vertices(Vlist& vs, Blist& rs)
    {
        if (vs.size() != rs.size())
            throw ValueException("vertex and group lists do not have the same size");

        typedef typename graph_traits<g_t>::vertex_descriptor vertex_t;

        gt_hash_map<vertex_t, size_t> vset;
        for (size_t i = 0; i < vs.size(); ++i)
            vset[vs[i]] = rs[i];

        typedef typename graph_traits<g_t>::edge_descriptor edges_t;

        gt_hash_set<edges_t> eset;
        for (auto vr : vset)
        {
            auto v = vr.first;
            for (auto e : all_edges_range(v, _g))
            {
                auto u = (source(e, _g) == v) ? target(e, _g) : source(e, _g);
                if (vset.find(u) != vset.end())
                    eset.insert(e);
            }
        }

        for (auto vr : vset)
            add_vertex(vr.first, vr.second,
                       [&](auto& e){ return eset.find(e) != eset.end(); });

        for (auto e : eset)
        {
            vertex_t v = source(e, _g);
            vertex_t u = target(e, _g);
            vertex_t r = vset[v];
            vertex_t s = vset[u];

            auto me = _emat.get_me(r, s);

            if (me == _emat.get_null_edge())
            {
                me = boost::add_edge(r, s, _bg).first;
                _emat.put_me(r, s, me);
                _c_mrs[me] = 0;
                for (size_t i = 0; i < _rec_types.size(); ++i)
                {
                    _c_brec[i][me] = 0;
                    _c_bdrec[i][me] = 0;
                }
            }

            assert(me == _emat.get_me(r, s));

            auto ew = _eweight[e];

            _mrs[me] += ew;
            _mrp[r] += ew;
            _mrm[s] += ew;

            for (size_t i = 0; i < _rec_types.size(); ++i)
            {
                switch (_rec_types[i])
                {
                case weight_type::REAL_NORMAL: // signed weights
                    _bdrec[i][me] += _drec[i][e];
                    [[gnu::fallthrough]];
                default:
                    _brec[i][me] += _rec[i][e];
                }
            }
        }
    }

    void add_vertices(python::object ovs, python::object ors)
    {
        multi_array_ref<uint64_t, 1> vs = get_array<uint64_t, 1>(ovs);
        multi_array_ref<uint64_t, 1> rs = get_array<uint64_t, 1>(ors);
        add_vertices(vs, rs);
    }

    bool allow_move(size_t r, size_t nr, bool allow_empty = true)
    {
        if (allow_empty)
            return ((_bclabel[r] == _bclabel[nr]) || (_wr[nr] == 0));
        else
            return _bclabel[r] == _bclabel[nr];
    }

    // move a vertex from its current block to block nr
    void move_vertex(size_t v, size_t r, size_t nr)
    {
        if (r == nr)
            return;

        if (!allow_move(r, nr))
            throw ValueException("cannot move vertex across clabel barriers");

        if (_coupled_state != nullptr && _vweight[v] > 0)
        {
            if (_wr[r] == _vweight[v])
            {
                _coupled_state->remove_partition_node(r, _bclabel[r]);
                _coupled_state->set_vertex_weight(r, 0);
            }

            if (_wr[nr] == 0)
            {
                _coupled_state->set_vertex_weight(nr, 1);
                _coupled_state->add_partition_node(nr, _bclabel[r]);
                _bclabel[nr] = _bclabel[r];
            }
        }

        remove_vertex(v, r, [](auto&) {return false;});
        add_vertex(v, nr, [](auto&) {return false;});
    }

    void move_vertex(size_t v, size_t nr)
    {
        size_t r = _b[v];
        move_vertex(v, r, nr);
    }

    void set_vertex_weight(size_t v, int w)
    {
        set_vertex_weight(v, w, _vweight);
    }

    void set_vertex_weight(size_t, int, vcmap_t&)
    {
        throw ValueException("Cannot set the weight of an unweighted state");
    }

    template <class VMap>
    void set_vertex_weight(size_t v, int w, VMap&& vweight)
    {
        vweight[v] = w;
    }

    void init_vertex_weight(size_t v)
    {
        init_vertex_weight(v, _vweight);
    }

    void init_vertex_weight(size_t, vcmap_t&)
    {
    }

    template <class VMap>
    void init_vertex_weight(size_t v, VMap&& vweight)
    {
        vweight.resize(num_vertices(_g));
        vweight[v] = 0;
    }

    template <class Vec>
    void move_vertices(Vec& v, Vec& nr)
    {
        for (size_t i = 0; i < std::min(v.size(), nr.size()); ++i)
            move_vertex(v[i], nr[i]);
    }

    void move_vertices(python::object ovs, python::object ors)
    {
        multi_array_ref<uint64_t, 1> vs = get_array<uint64_t, 1>(ovs);
        multi_array_ref<uint64_t, 1> rs = get_array<uint64_t, 1>(ors);
        if (vs.size() != rs.size())
            throw ValueException("vertex and group lists do not have the same size");
        move_vertices(vs, rs);
    }

    template <class VMap>
    void set_partition(VMap&& b)
    {
        for (auto v : vertices_range(_g))
            move_vertex(v, b[v]);
    }

    void set_partition(boost::any& ab)
    {
        vmap_t& b = boost::any_cast<vmap_t&>(ab);
        set_partition<typename vmap_t::unchecked_t>(b.get_unchecked());
    }

    size_t virtual_remove_size(size_t v)
    {
        return _wr[_b[v]] - _vweight[v];
    }

    // merge vertex u into v
    void merge_vertices(size_t u, size_t v)
    {
        typedef typename graph_traits<g_t>::edge_descriptor edge_t;
        UnityPropertyMap<int, edge_t> dummy;
        merge_vertices(u, v, dummy);
    }

    template <class Emap>
    void merge_vertices(size_t u, size_t v, Emap&& ec)
    {
        merge_vertices(u, v, ec, _is_weighted);
    }

    template <class Emap>
    void merge_vertices(size_t, size_t, Emap&&, std::false_type)
    {
        throw ValueException("cannot merge vertices of unweighted graph");
    }

    template <class Emap>
    void merge_vertices(size_t u, size_t v, Emap&& ec, std::true_type)
    {
        if (u == v)
            return;

        auto eweight_c = _eweight.get_checked();
        std::vector<typename rec_t::value_type::checked_t> c_rec;
        std::vector<typename brec_t::value_type::checked_t> c_drec;
        for (auto& p : _rec)
            c_rec.push_back(p.get_checked());
        for (auto& p : _drec)
            c_drec.push_back(p.get_checked());

        typedef typename graph_traits<g_t>::vertex_descriptor vertex_t;
        typedef typename graph_traits<g_t>::edge_descriptor edge_t;

        gt_hash_map<std::tuple<vertex_t, int>, vector<edge_t>> ns_u, ns_v;
        for(auto e : out_edges_range(u, _g))
            ns_u[std::make_tuple(target(e, _g), ec[e])].push_back(e);
        for(auto e : out_edges_range(v, _g))
            ns_v[std::make_tuple(target(e, _g), ec[e])].push_back(e);

        size_t nrec = this->_rec_types.size();
        std::vector<double> ecc(nrec), decc(nrec);

        for(auto& kv : ns_u)
        {
            vertex_t t = get<0>(kv.first);
            int l = get<1>(kv.first);
            auto& es = kv.second;

            size_t w = 0;

            std::fill(ecc.begin(), ecc.end(), 0);
            std::fill(decc.begin(), decc.end(), 0);
            for (auto& e : es)
            {
                w += _eweight[e];
                for (size_t i = 0; i < nrec; ++i)
                {
                    ecc[i] += _rec[i][e];
                    decc[i] += _drec[i][e];
                }
            }

            if (t == u)
            {
                t = v;
                if (!is_directed::apply<g_t>::type::value)
                {
                    assert(w % 2 == 0);
                    w /= 2;
                    for (size_t i = 0; i < nrec; ++i)
                    {
                        ecc[i] /= 2;
                        decc[i] /= 2;
                    }
                }
            }

            auto iter = ns_v.find(std::make_tuple(t, l));
            if (iter != ns_v.end())
            {
                auto& e = iter->second.front();
                _eweight[e] += w;
                for (size_t i = 0; i < nrec; ++i)
                {
                    _rec[i][e] += ecc[i];
                    _drec[i][e] += decc[i];
                }
                assert(ec[e] == l);
            }
            else
            {
                auto e = boost::add_edge(v, t, _g).first;
                ns_v[std::make_tuple(t, l)].push_back(e);
                eweight_c[e] = w;
                for (size_t i = 0; i < nrec; ++i)
                {
                    c_rec[i][e] = ecc[i];
                    c_drec[i][e] = decc[i];
                }
                set_prop(ec, e, l);
                assert(ec[e] == l);
            }
        }

        if (is_directed::apply<g_t>::type::value)
        {
            ns_u.clear();
            ns_v.clear();

            for(auto e : in_edges_range(v, _g))
                ns_v[std::make_tuple(source(e, _g), ec[e])].push_back(e);
            for(auto e : in_edges_range(u, _g))
                ns_u[std::make_tuple(source(e, _g), ec[e])].push_back(e);

            for(auto& kv : ns_u)
            {
                vertex_t s = get<0>(kv.first);
                int l = get<1>(kv.first);
                auto& es = kv.second;

                if (s == u)
                    continue;

                size_t w = 0;
                std::fill(ecc.begin(), ecc.end(), 0);
                std::fill(decc.begin(), decc.end(), 0);
                for (auto& e : es)
                {
                    w += _eweight[e];
                    for (size_t i = 0; i < nrec; ++i)
                    {
                        ecc[i] += _rec[i][e];
                        decc[i] += _drec[i][e];
                    }
                }

                auto iter = ns_v.find(std::make_tuple(s, l));
                if (iter != ns_v.end())
                {
                    auto& e = iter->second.front();
                    _eweight[e] += w;
                    for (size_t i = 0; i < nrec; ++i)
                    {
                        _rec[i][e] += ecc[i];
                        _drec[i][e] += decc[i];
                    }
                    assert(ec[e] == l);
                }
                else
                {
                    auto e = boost::add_edge(s, v, _g).first;
                    ns_v[std::make_tuple(s, l)].push_back(e);
                    eweight_c[e] = w;
                    for (size_t i = 0; i < nrec; ++i)
                    {
                        c_rec[i][e] = ecc[i];
                        c_drec[i][e] = decc[i];
                    }
                    set_prop(ec, e, l);
                    assert(ec[e] == l);
                }
            }
        }

        _vweight[v] +=_vweight[u];
        _vweight[u] = 0;
        for (auto e : all_edges_range(u, _g))
        {
            _eweight[e] = 0;
            set_prop(ec, e, 0);
            for (size_t i = 0; i < nrec; ++i)
            {
                _rec[i][e] = 0;
                _drec[i][e] = 0;
            }
        }
        clear_vertex(u, _g);
        _merge_map[u] = v;
        merge_degs(u, v, _degs);
    }

    template <class EMap, class Edge, class Val>
    void set_prop(EMap& ec, Edge& e, Val&& val)
    {
        ec[e] = val;
    }

    template <class Edge, class Val>
    void set_prop(UnityPropertyMap<typename std::remove_reference<Val>::type, Edge>&,
                  Edge&, Val&&)
    {
    }

    void merge_degs(size_t, size_t, const simple_degs_t&) {}

    void merge_degs(size_t u, size_t v, typename degs_map_t::unchecked_t& degs)
    {
        gt_hash_map<std::tuple<size_t, size_t>, size_t> hist;
        for (auto& kn : degs[u])
            hist[make_tuple(get<0>(kn), get<1>(kn))] += get<2>(kn);
        for (auto& kn : degs[v])
            hist[make_tuple(get<0>(kn), get<1>(kn))] += get<2>(kn);
        degs[u].clear();
        degs[v].clear();
        auto& d = degs[v];
        for (auto& kn : hist)
            d.emplace_back(get<0>(kn.first), get<1>(kn.first), kn.second);
    }

    size_t add_block()
    {
        size_t r = boost::add_vertex(_bg);
        _wr.resize(num_vertices(_bg));
        _mrm.resize(num_vertices(_bg));
        _mrp.resize(num_vertices(_bg));
        _wr[r] = _mrm[r] = _mrp[r] = 0;
        _bclabel.resize(num_vertices(_bg));
        _brecsum.resize(num_vertices(_bg));
        _empty_pos.resize(num_vertices(_bg));
        _candidate_pos.resize(num_vertices(_bg));
        add_element(_empty_blocks, _empty_pos, r);
        for (auto& p : _partition_stats)
            p.add_block();
        _bignore_degrees.resize(num_vertices(_bg));
        if (!_egroups.empty())
            _egroups.init(_b, _eweight, _g, _bg);
        if (_coupled_state != nullptr)
            _coupled_state->coupled_resize_vertex(r);
        sync_emat();
        return r;
    }

    void coupled_resize_vertex(size_t v)
    {
        _b.resize(num_vertices(_g));
        init_vertex_weight(v);
        _pclabel.resize(num_vertices(_g));
        _ignore_degrees.resize(num_vertices(_g));
        resize_degs(_degs);
    }

    void resize_degs(const simple_degs_t&) {}

    void resize_degs(typename degs_map_t::unchecked_t& degs)
    {
        degs.resize(num_vertices(_g));
    }

    // =========================================================================
    // Virtual state modification
    // =========================================================================

    // compute the entropy difference of a virtual move of vertex from block r
    // to nr
    template <bool exact, class MEntries>
    double virtual_move_sparse(size_t v, size_t r, size_t nr,
                               MEntries& m_entries)
    {
        if (r == nr)
            return 0.;

        double dS = entries_dS<exact>(m_entries, _mrs, _emat, _bg);

        size_t kout = out_degreeS()(v, _g, _eweight);
        size_t kin = kout;
        if (is_directed::apply<g_t>::type::value)
            kin = in_degreeS()(v, _g, _eweight);

        int dwr = _vweight[v];
        int dwnr = dwr;

        if (r == null_group && dwnr == 0)
            dwnr = 1;

        auto vt = [&](auto mrp, auto mrm, auto nr)
            {
                assert(mrp >= 0 && mrm >=0 && nr >= 0);
                if (exact)
                    return vterm_exact(mrp, mrm, nr, _deg_corr, _bg);
                else
                    return vterm(mrp, mrm, nr, _deg_corr, _bg);
            };

        if (r != null_group)
        {
            dS += vt(_mrp[r]  - kout, _mrm[r]  - kin, _wr[r]  - dwr );
            dS -= vt(_mrp[r]        , _mrm[r]       , _wr[r]        );
        }

        if (nr != null_group)
        {
            dS += vt(_mrp[nr] + kout, _mrm[nr] + kin, _wr[nr] + dwnr);
            dS -= vt(_mrp[nr]       , _mrm[nr]      , _wr[nr]       );
        }

        return dS;
    }

    template <bool exact>
    double virtual_move_sparse(size_t v, size_t r, size_t nr)
    {
        return virtual_move_sparse<exact>(v, r, nr);
    }

    double virtual_move_dense(size_t v, size_t r, size_t nr, bool multigraph)
    {
        if (_deg_corr)
            throw GraphException("Dense entropy for degree corrected model not implemented!");

        typedef typename graph_traits<g_t>::vertex_descriptor vertex_t;

        if (r == nr)
            return 0;

        int kin = 0, kout = 0;
        kout += out_degreeS()(v, _g, _eweight);
        if (is_directed::apply<g_t>::type::value)
            kin += in_degreeS()(v, _g, _eweight);

        vector<int> deltap(num_vertices(_bg), 0);
        int deltal = 0;
        for (auto e : out_edges_range(v, _g))
        {
            vertex_t u = target(e, _g);
            vertex_t s = _b[u];
            if (u == v)
                deltal += _eweight[e];
            else
                deltap[s] += _eweight[e];
        }
        if (!is_directed::apply<g_t>::type::value)
            deltal /= 2;

        vector<int> deltam(num_vertices(_bg), 0);
        for (auto e : in_edges_range(v, _g))
        {
            vertex_t u = source(e, _g);
            if (u == v)
                continue;
            vertex_t s = _b[u];
            deltam[s] += _eweight[e];
        }

        double dS = 0;
        int dwr = _vweight[v];
        int dwnr = dwr;

        if (r == null_group && dwnr == 0)
            dwnr = 1;

        if (nr == null_group)
        {
            std::fill(deltap.begin(), deltap.end(), 0);
            std::fill(deltam.begin(), deltam.end(), 0);
            deltal = 0;
        }

        double Si = 0, Sf = 0;
        for (vertex_t s = 0; s < num_vertices(_bg); ++s)
        {
            int ers = (r != null_group) ? get_beprop(r, s, _mrs, _emat) : 0;
            int enrs = (nr != null_group) ? get_beprop(nr, s, _mrs, _emat) : 0;

            if (!is_directed::apply<g_t>::type::value)
            {
                if (s != nr && s != r)
                {
                    if (r != null_group)
                    {
                        Si += eterm_dense(r,  s, ers,              _wr[r],         _wr[s], multigraph, _bg);
                        Sf += eterm_dense(r,  s, ers - deltap[s],  _wr[r] - dwr,   _wr[s], multigraph, _bg);
                    }

                    if (nr != null_group)
                    {
                        Si += eterm_dense(nr, s, enrs,             _wr[nr],        _wr[s], multigraph, _bg);
                        Sf += eterm_dense(nr, s, enrs + deltap[s], _wr[nr] + dwnr, _wr[s], multigraph, _bg);
                    }
                }

                if (s == r)
                {
                    Si += eterm_dense(r, r, ers,                      _wr[r],       _wr[r],       multigraph, _bg);
                    Sf += eterm_dense(r, r, ers - deltap[r] - deltal, _wr[r] - dwr, _wr[r] - dwr, multigraph, _bg);
                }

                if (s == nr)
                {
                    Si += eterm_dense(nr, nr, enrs,                       _wr[nr],        _wr[nr],        multigraph, _bg);
                    Sf += eterm_dense(nr, nr, enrs + deltap[nr] + deltal, _wr[nr] + dwnr, _wr[nr] + dwnr, multigraph, _bg);

                    if (r != null_group)
                    {
                        Si += eterm_dense(r, nr, ers,                          _wr[r],       _wr[nr],        multigraph, _bg);
                        Sf += eterm_dense(r, nr, ers - deltap[nr] + deltap[r], _wr[r] - dwr, _wr[nr] + dwnr, multigraph, _bg);
                    }
                }
            }
            else
            {
                int esr = (r != null_group) ? get_beprop(s, r, _mrs, _emat) : 0;
                int esnr  = (nr != null_group) ? get_beprop(s, nr, _mrs, _emat) : 0;

                if (s != nr && s != r)
                {
                    if (r != null_group)
                    {
                        Si += eterm_dense(r, s, ers            , _wr[r]      , _wr[s]      , multigraph, _bg);
                        Sf += eterm_dense(r, s, ers - deltap[s], _wr[r] - dwr, _wr[s]      , multigraph, _bg);
                        Si += eterm_dense(s, r, esr            , _wr[s]      , _wr[r]      , multigraph, _bg);
                        Sf += eterm_dense(s, r, esr - deltam[s], _wr[s]      , _wr[r] - dwr, multigraph, _bg);
                    }

                    if (nr != null_group)
                    {
                        Si += eterm_dense(nr, s, enrs            , _wr[nr]       , _wr[s]        , multigraph, _bg);
                        Sf += eterm_dense(nr, s, enrs + deltap[s], _wr[nr] + dwnr, _wr[s]        , multigraph, _bg);
                        Si += eterm_dense(s, nr, esnr            , _wr[s]        , _wr[nr]       , multigraph, _bg);
                        Sf += eterm_dense(s, nr, esnr + deltam[s], _wr[s]        , _wr[nr] + dwnr, multigraph, _bg);
                    }
                }

                if(s == r)
                {
                    Si += eterm_dense(r, r, ers                                  , _wr[r]      , _wr[r]      , multigraph, _bg);
                    Sf += eterm_dense(r, r, ers - deltap[r]  - deltam[r] - deltal, _wr[r] - dwr, _wr[r] - dwr, multigraph, _bg);

                    if (nr != null_group)
                    {
                        Si += eterm_dense(r, nr, esnr                         , _wr[r]      , _wr[nr]       , multigraph, _bg);
                        Sf += eterm_dense(r, nr, esnr - deltap[nr] + deltam[r], _wr[r] - dwr, _wr[nr] + dwnr, multigraph, _bg);
                    }
                }

                if(s == nr)
                {
                    Si += eterm_dense(nr, nr, esnr                                   , _wr[nr]       , _wr[nr]       , multigraph, _bg);
                    Sf += eterm_dense(nr, nr, esnr + deltap[nr] + deltam[nr] + deltal, _wr[nr] + dwnr, _wr[nr] + dwnr, multigraph, _bg);

                    if (r != null_group)
                    {
                        Si += eterm_dense(nr, r, esr                         , _wr[nr]       , _wr[r]      , multigraph, _bg);
                        Sf += eterm_dense(nr, r, esr + deltap[r] - deltam[nr], _wr[nr] + dwnr, _wr[r] - dwr, multigraph, _bg);
                    }
                }
            }
        }

        return Sf - Si + dS;
    }


    template <class MEntries>
    double virtual_move(size_t v, size_t r, size_t nr, entropy_args_t ea,
                        MEntries& m_entries)
    {
        assert(size_t(_b[v]) == r || r == null_group);

        if (r == nr)
            return 0;

        if (r != null_group && nr != null_group && !allow_move(r, nr))
            return std::numeric_limits<double>::infinity();

        get_move_entries(v, r, nr, m_entries, [](auto) { return false; });

        double dS = 0;
        if (ea.adjacency)
        {
            if (ea.dense)
            {
                dS = virtual_move_dense(v, r, nr, ea.multigraph);
            }
            else
            {
                if (ea.exact)
                    dS = virtual_move_sparse<true>(v, r, nr, m_entries);
                else
                    dS = virtual_move_sparse<false>(v, r, nr, m_entries);
            }
        }

        if (ea.partition_dl || ea.degree_dl || ea.edges_dl)
        {
            enable_partition_stats();
            auto& ps = get_partition_stats(v);
            if (ea.partition_dl)
                dS += ps.get_delta_partition_dl(v, r, nr, _vweight);
            if (_deg_corr && ea.degree_dl)
                dS += ps.get_delta_deg_dl(v, r, nr, _vweight, _eweight,
                                          _degs, _g, ea.degree_dl_kind);
            if (ea.edges_dl)
            {
                size_t actual_B = 0;
                for (auto& ps : _partition_stats)
                    actual_B += ps.get_actual_B();
                dS += ps.get_delta_edges_dl(v, r, nr, _vweight, actual_B,
                                            _g);
            }
        }

        int dL = 0;
        if (ea.recs)
        {
            auto positive_entries_op = [&](size_t i, auto&& w_log_P,
                                           auto&& w_log_prior)
                {
                    int dB_E = 0;
                    entries_op(m_entries, this->_emat,
                               [&](auto, auto, auto& me, auto& delta)
                               {
                                   double ers = 0;
                                   double xrs = 0;
                                   if (me != _emat.get_null_edge())
                                   {
                                       ers = this->_brec[0][me];
                                       xrs = this->_brec[i][me];
                                   }
                                   auto d = get<1>(delta)[0];
                                   auto dx = get<1>(delta)[i];
                                   dS -= -w_log_P(ers, xrs);
                                   dS += -w_log_P(ers + d, xrs + dx);

                                   if (ea.recs_dl)
                                   {
                                       size_t ers = 0;
                                       if (me != _emat.get_null_edge())
                                           ers = this->_mrs[me];
                                       if (ers == 0 && get<0>(delta) > 0)
                                           dB_E++;
                                       if (ers > 0 && ers + get<0>(delta) == 0)
                                           dB_E--;
                                   }
                               });
                    if (dB_E != 0 && ea.recs_dl && std::isnan(_wparams[i][0])
                        && std::isnan(_wparams[i][1]))
                    {
                        dS -= -w_log_prior(_B_E);
                        dS += -w_log_prior(_B_E + dB_E);
                    }
                };

            for (size_t i = 0; i < _rec_types.size(); ++i)
            {
                auto& wp = _wparams[i];
                switch (_rec_types[i])
                {
                case weight_type::COUNT:
                    break;
                case weight_type::REAL_EXPONENTIAL:
                    positive_entries_op(i,
                                        [&](auto N, auto x)
                                        { return positive_w_log_P(N, x, wp[0],
                                                                  wp[1],
                                                                  this->_epsilon[i]);
                                        },
                                        [&](size_t B_E)
                                        { return positive_w_log_P(B_E,
                                                                  _recsum[i],
                                                                  wp[0], wp[1],
                                                                  this->_epsilon[i]);
                                        });
                    break;
                case weight_type::DISCRETE_GEOMETRIC:
                    positive_entries_op(i,
                                        [&](auto N, auto x)
                                        { return geometric_w_log_P(N, x, wp[0],
                                                                   wp[1]);
                                        },
                                        [&](size_t B_E)
                                        { return geometric_w_log_P(B_E,
                                                                   _recsum[i],
                                                                   wp[0],
                                                                   wp[1]);
                                        });
                    break;
                case weight_type::DISCRETE_POISSON:
                    positive_entries_op(i,
                                        [&](auto N, auto x)
                                        { return poisson_w_log_P(N, x, wp[0],
                                                                 wp[1]);
                                        },
                                        [&](size_t B_E)
                                        { return geometric_w_log_P(B_E,
                                                                   _recsum[i],
                                                                   wp[0],
                                                                   wp[1]);
                                        });
                    break;
                case weight_type::DISCRETE_BINOMIAL:
                    positive_entries_op(i,
                                        [&](auto N, auto x)
                                        { return binomial_w_log_P(N, x, wp[0],
                                                                  wp[1], wp[2]);
                                        },
                                        [&](size_t B_E)
                                        { return geometric_w_log_P(B_E,
                                                                   _recsum[i],
                                                                   wp[1],
                                                                   wp[2]);
                                        });
                    break;
                case weight_type::REAL_NORMAL:
                    {
                        int dB_E = 0;
                        int dB_E_D = 0;
                        double dBx2 = 0;
                        _dBdx[i] = 0;
                        entries_op(m_entries, _emat,
                                   [&](auto, auto, auto& me, auto& delta)
                                   {
                                       double ers = 0;
                                       double xrs = 0, x2rs = 0;
                                       if (me != _emat.get_null_edge())
                                       {
                                           ers = this->_brec[0][me];
                                           xrs = this->_brec[i][me];
                                           x2rs = this->_bdrec[i][me];
                                       }
                                       auto d = get<1>(delta)[0];
                                       auto dx = get<1>(delta)[i];
                                       auto dx2 = get<2>(delta)[i];
                                       dS -= -signed_w_log_P(ers, xrs, x2rs,
                                                             wp[0], wp[1],
                                                             wp[2], wp[3],
                                                             this->_epsilon[i]);
                                       dS += -signed_w_log_P(ers + d,
                                                             xrs + dx,
                                                             x2rs + dx2,
                                                             wp[0], wp[1],
                                                             wp[2], wp[3],
                                                             this->_epsilon[i]);
                                       if (std::isnan(wp[0]) &&
                                           std::isnan(wp[1]))
                                       {
                                           auto n_ers = ers + get<1>(delta)[0];
                                           if (ers == 0 && n_ers > 0)
                                               dB_E++;
                                           if (ers > 0 && n_ers == 0)
                                               dB_E--;
                                           if (n_ers > 1)
                                           {
                                               if (ers < 2)
                                                   dB_E_D++;
                                               _dBdx[i] += \
                                                   (x2rs + dx2 -
                                                    std::pow(xrs + dx, 2) / n_ers);

                                           }
                                           if (ers > 1)
                                           {
                                               if (n_ers < 2)
                                                   dB_E_D--;
                                               _dBdx[i] -= \
                                                   (x2rs -
                                                    std::pow(xrs, 2) / ers);
                                           }
                                           dBx2 += (std::pow(xrs + dx, 2) -
                                                    std::pow(xrs, 2));
                                       }
                                   });

                        if (std::isnan(wp[0]) && std::isnan(wp[1]))
                        {
                            if (ea.recs_dl && (dB_E != 0 || dBx2 != 0))
                            {
                                dS -= -signed_w_log_P(_B_E, _recsum[i],
                                                      _recx2[i], wp[0], wp[1],
                                                      wp[2], wp[3], _epsilon[i]);
                                dS += -signed_w_log_P(_B_E + dB_E, _recsum[i],
                                                      _recx2[i] + dBx2, wp[0],
                                                      wp[1], wp[2], wp[3],
                                                      _epsilon[i]);
                            }

                            if (dB_E_D != 0 || _dBdx[i] != 0)
                            {
                                dS -= -positive_w_log_P(_B_E_D, _recdx[i],
                                                        wp[2], wp[3],
                                                        _epsilon[i]);
                                dS += -positive_w_log_P(_B_E_D + dB_E_D,
                                                        _recdx[i] + _dBdx[i],
                                                        wp[2], wp[3],
                                                        _epsilon[i]);
                            }

                            if (dL == 0)
                            {
                                if (_B_E_D == 0 && dB_E_D > 0)
                                    dL++;
                                if (_B_E_D > 0 && _B_E_D + dB_E_D == 0)
                                    dL--;
                            }

                            if (_Lrecdx[0] >= 0)
                            {
                                size_t N_B_E_D = _B_E_D + dB_E_D;

                                dS -= -safelog(_B_E_D);
                                dS += -safelog(N_B_E_D);

                                _dBdx[i] = _recdx[i] * dB_E_D + _dBdx[i] * N_B_E_D;

                                if (_coupled_state == nullptr)
                                {
                                    size_t L = _Lrecdx[0];
                                    dS -= -positive_w_log_P(L, _Lrecdx[i+1],
                                                            wp[2], wp[3],
                                                            _epsilon[i]);
                                    dS += -positive_w_log_P(L + dL,
                                                            _Lrecdx[i+1] + _dBdx[i],
                                                            wp[2], wp[3],
                                                            _epsilon[i]);
                                }
                            }
                        }
                    }
                    break;
                case weight_type::DELTA_T: // waiting times
                    if ((r != nr) && _ignore_degrees[v] > 0)
                    {
                        auto dt = out_degreeS()(v, _g, _rec[i]);
                        int k = out_degreeS()(v, _g, _eweight);
                        if (r != null_group)
                        {
                            dS -= -positive_w_log_P(_mrp[r], _brecsum[r],
                                                    wp[0], wp[1],
                                                    _epsilon[i]);
                            dS += -positive_w_log_P(_mrp[r] - k,
                                                    _brecsum[r] - dt,
                                                    wp[0], wp[1],
                                                    _epsilon[i]);
                        }
                        if (nr != null_group)
                        {
                            dS -= -positive_w_log_P(_mrp[nr], _brecsum[nr],
                                                    wp[0], wp[1],
                                                    _epsilon[i]);
                            dS += -positive_w_log_P(_mrp[nr] + k,
                                                    _brecsum[nr] + dt,
                                                    wp[0], wp[1],
                                                    _epsilon[i]);
                        }
                    }
                    break;
                }
            }
        }

        if (_coupled_state != nullptr && _vweight[v] > 0)
        {
            assert(r == null_group || nr == null_group || allow_move(r, nr));
            bool r_vacate = (r != null_group) && (_wr[r] == _vweight[v]);
            bool nr_occupy = (nr != null_group) && (_wr[nr] == 0);
            //if (ea.partition_dl && r_vacate != nr_occupy)
            if (r_vacate != nr_occupy)
            {
                scoped_lock lck(_lock);
                if (r_vacate)
                {
                    dS += _coupled_state->virtual_move(r,
                                                       _bclabel[r],
                                                       null_group,
                                                       _coupled_entropy_args);
                }

                if (nr_occupy)
                {
                    dS += _coupled_state->virtual_move(nr,
                                                       null_group,
                                                       _bclabel[r],
                                                       _coupled_entropy_args);
                }
            }

            if (ea.recs && !_rec_types.empty())
            {
                auto& recs_entries = m_entries._recs_entries;
                recs_entries.clear();
                entries_op(m_entries, _emat,
                           [&](auto r, auto s, auto& me, auto& delta)
                           {
                               recs_entries.emplace_back(r, s, me,
                                                         get<0>(delta),
                                                         get<1>(delta));
                           });

                scoped_lock lck(_lock);
                dS += _coupled_state->recs_dS(r, nr, recs_entries, _dBdx, dL);
            }
        }

        return dS;
    }

    double virtual_move(size_t v, size_t r, size_t nr, entropy_args_t ea)
    {
        return virtual_move(v, r, nr, ea, _m_entries);
    }

    double recs_dS(size_t u, size_t v,
                   const std::vector<std::tuple<size_t, size_t,
                                                GraphInterface::edge_t, int,
                                                std::vector<double>>>& entries,
                   std::vector<double>& dBdx, int dL)
    {
        if (_rec_types.empty())
            return 0;

        if (_vweight[v] == 0)
            _b[v] = _b[u];

        _m_entries.set_move(_b[u], _b[v],
                            num_vertices(_bg));

        for (auto& iter : entries)
        {
            size_t r = _b[get<0>(iter)];
            size_t s = _b[get<1>(iter)];

            auto& e = get<2>(iter);

            int d = get<3>(iter);
            auto dx = get<4>(iter);

            if (e == _emat.get_null_edge())
            {
                for (size_t i = 0; i < _rec_types.size(); ++i)
                    dx[i] = std::pow(dx[i], 2);

                _m_entries.template insert_delta<true>(r, s, d > 0, dx);
            }
            else
            {
                for (size_t i = 0; i < _rec_types.size(); ++i)
                {
                    auto x = _rec[i][e];
                    dx[i] = (std::pow(x + dx[i], 2) -
                             std::pow(x, 2));
                }

                int ers = _eweight[e];
                if (ers == 0 && d > 0)
                {
                    assert(get<3>(iter) > 0);
                    _m_entries.template insert_delta<true>(r, s, 1);
                }
                else
                {
                    if (ers > 0 && ers + d == 0)
                        _m_entries.template insert_delta<false>(r, s, 1);
                }
                _m_entries.template insert_delta<true>(r, s, 0, dx);
            }
        }

        double dS = 0;
        auto w_entries_op = [&](auto&& w_log_P)
            {
                entries_op(_m_entries, _emat,
                           [&](auto, auto, auto& me, auto& delta)
                           {
                               int ers = 0;
                               if (me != _emat.get_null_edge())
                                   ers = this->_brec[0][me];
                               auto d = get<0>(delta);
                               if (d != 0)
                               {
                                   dS -= -w_log_P(ers, me);
                                   dS += -w_log_P(ers + d, me);
                               }
                           });
            };

        for (size_t i = 0; i < _rec_types.size(); ++i)
        {
            auto& wp = _wparams[i];
            switch (_rec_types[i])
            {
            case weight_type::COUNT:
                break;
            case weight_type::REAL_EXPONENTIAL:
                w_entries_op([&](auto N, auto& me)
                             {
                                 double x = 0;
                                 if (me != _emat.get_null_edge())
                                     x = this->_brec[i][me];
                                 return positive_w_log_P(N, x, wp[0], wp[1],
                                                         this->_epsilon[i]);
                             });
                break;
            case weight_type::DISCRETE_GEOMETRIC:
                w_entries_op([&](auto N, auto& me)
                             {
                                 double x = 0;
                                 if (me != _emat.get_null_edge())
                                     x = this->_brec[i][me];
                                 return geometric_w_log_P(N, x, wp[0],
                                                          wp[1]);
                             });
                break;
            case weight_type::REAL_NORMAL:
                {
                    int dB_E_D = 0;
                    double drecdx = 0;
                    entries_op(_m_entries, _emat,
                               [&](auto, auto, auto& me, auto& delta)
                               {
                                   int ers = 0;
                                   double x = 0, x2 = 0;
                                   if (me != _emat.get_null_edge())
                                   {
                                       ers = this->_brec[0][me];
                                       x = this->_brec[i][me];
                                       x2 = this->_bdrec[i][me];
                                   }
                                   auto d = get<0>(delta);
                                   auto dx2 = get<1>(delta)[i];
                                   dS -= -signed_w_log_P(ers, x, x2, wp[0],
                                                         wp[1], wp[2], wp[3],
                                                         this->_epsilon[i]);
                                   dS += -signed_w_log_P(ers + d, x, x2 + dx2,
                                                         wp[0], wp[1], wp[2],
                                                         wp[3],
                                                         this->_epsilon[i]);
                                   if (ers > 1)
                                   {
                                       dB_E_D--;
                                       drecdx -= \
                                           (this->_bdrec[i][me] -
                                            std::pow(this->_brec[i][me], 2) / ers);
                                   }
                                   if (ers + d > 1)
                                   {
                                       dB_E_D++;
                                       drecdx += \
                                           (this->_bdrec[i][me] + dx2 -
                                            std::pow(this->_brec[i][me], 2) / (ers + d));
                                   }
                               });

                    if (dB_E_D != 0 || drecdx != 0 || dBdx[i] != 0 || dL != 0)
                    {
                        dS -= -positive_w_log_P(_B_E_D, _recdx[i], wp[2],
                                                wp[3], _epsilon[i]);
                        dS += -positive_w_log_P(_B_E_D + dB_E_D,
                                                _recdx[i] + drecdx, wp[2],
                                                wp[3], _epsilon[i]);
                        if (_Lrecdx[0] >= 0)
                        {
                            size_t L = _Lrecdx[0];
                            size_t N_B_E_D = _B_E_D + dB_E_D;
                            int ddL = 0;
                            if (_B_E_D == 0 && N_B_E_D > 0)
                                ddL++;
                            if (_B_E_D > 0 && N_B_E_D == 0)
                                ddL--;

                            dS -= -positive_w_log_P(L, _Lrecdx[i+1], wp[2],
                                                    wp[3], _epsilon[i]);

                            auto dx = dBdx[i] + \
                                _recdx[i] * dB_E_D + drecdx * N_B_E_D;

                            dS += -positive_w_log_P(L + dL + ddL,
                                                    _Lrecdx[i+1] + dx, wp[2],
                                                    wp[3], _epsilon[i]);
                            dS -= -safelog(_B_E_D);
                            dS += -safelog(N_B_E_D);
                        }
                     }
                }
                break;
            default:
                throw GraphException("coupled rec type not implemented");
            }
        }
        return dS;
    }

    double get_delta_partition_dl(size_t v, size_t r, size_t nr)
    {
        enable_partition_stats();
        auto& ps = get_partition_stats(v);
        return ps.get_delta_partition_dl(v, r, nr, _vweight);
    }

    // =========================================================================
    // Move proposals
    // =========================================================================

    // Sample node placement
    template <class RNG>
    size_t sample_block(size_t v, double c, double d, RNG& rng)
    {
        // attempt random block
        size_t s;
        std::bernoulli_distribution new_r(d);
        if (new_r(rng) && (_candidate_blocks.size() - 1 < num_vertices(_g)))
        {
            if (_empty_blocks.empty())
                add_block();
            return uniform_sample(_empty_blocks, rng);
        }
        else
        {
            s = uniform_sample(_candidate_blocks.begin() + 1,
                               _candidate_blocks.end(),
                               rng);
        }

        if (!std::isinf(c) && !_neighbor_sampler.empty(v))
        {
            auto u = _neighbor_sampler.sample(v, rng);
            size_t t = _b[u];
            double p_rand = 0;
            if (c > 0)
            {
                size_t B = _candidate_blocks.size() - 1;
                if (is_directed::apply<g_t>::type::value)
                    p_rand = c * B / double(_mrp[t] + _mrm[t] + c * B);
                else
                    p_rand = c * B / double(_mrp[t] + c * B);
            }

            std::uniform_real_distribution<> rdist;
            if (c == 0 || rdist(rng) >= p_rand)
            {
                if (_egroups.empty())
                    _egroups.init(_b, _eweight, _g, _bg);
                const auto& e = _egroups.sample_edge(t, rng);
                s = _b[target(e, _g)];
                if (s == t)
                    s = _b[source(e, _g)];
                else
                    assert(size_t(_b[source(e, _g)]) == t);
            }
        }

        return s;
    }

    size_t sample_block(size_t v, double c, double d, rng_t& rng)
    {
        return sample_block<rng_t>(v, c, d, rng);
    }

    size_t random_neighbor(size_t v, rng_t& rng)
    {
        if (_neighbor_sampler.empty(v))
            return v;
        return _neighbor_sampler.sample(v, rng);
    }

    // Computes the move proposal probability
    template <class MEntries>
    double get_move_prob(size_t v, size_t r, size_t s, double c, double d,
                         bool reverse, MEntries& m_entries)
    {
        size_t B = _candidate_blocks.size() - 1;

        if (reverse)
        {
            if (_wr[s] == _vweight[v])
                return d;
            if (_wr[r] == 0)
                B++;
            // if (_wr[s] == _vweight[v])
            //     B--;
        }
        else
        {
            if (_wr[s] == 0)
                return d;
        }

        if (B == num_vertices(_g))
            d = 0;

        if (std::isinf(c))
            return (1. - d) / B;

        double p = 0;
        size_t w = 0;

        size_t kout = out_degreeS()(v, _g, _eweight);
        size_t kin = kout;
        if (is_directed::apply<g_t>::type::value)
            kin = in_degreeS()(v, _g, _eweight);
        m_entries.get_mes(_emat);

        auto sum_prob = [&](auto& e, auto u)
            {
                size_t t = _b[u];
                if (u == v)
                    t = r;
                size_t ew = _eweight[e];
                w += ew;

                int mts = 0;
                const auto& me = m_entries.get_me(t, s, _emat);
                if (me != _emat.get_null_edge())
                    mts = _mrs[me];
                int mtp = _mrp[t];
                int mst = mts;
                int mtm = mtp;

                if (is_directed::apply<g_t>::type::value)
                {
                    mst = 0;
                    const auto& me = m_entries.get_me(s, t, _emat);
                    if (me != _emat.get_null_edge())
                        mst = _mrs[me];
                    mtm = _mrm[t];
                }

                if (reverse)
                {
                    int dts = get<0>(m_entries.get_delta(t, s));
                    int dst = dts;
                    if (is_directed::apply<g_t>::type::value)
                        dst = get<0>(m_entries.get_delta(s, t));

                    mts += dts;
                    mst += dst;

                    if (t == s)
                    {
                        mtp -= kout;
                        mtm -= kin;
                    }

                    if (t == r)
                    {
                        mtp += kout;
                        mtm += kin;
                    }
                }

                if (is_directed::apply<g_t>::type::value)
                {
                    p += ew * ((mts + mst + c) / (mtp + mtm + c * B));
                }
                else
                {
                    if (t == s)
                        mts *= 2;
                    p += ew * (mts + c) / (mtp + c * B);
                }
            };

        // self-loops are always ignored when sampling neighbors
        for (auto e : out_edges_range(v, _g))
        {
            if (target(e, _g) == v)
                continue;
            sum_prob(e, target(e, _g));
        }

        for (auto e : in_edges_range(v, _g))
        {
            if (source(e, _g) == v)
                continue;
            sum_prob(e, source(e, _g));
        }

        if (w > 0)
            return (1. - d) * p / w;
        else
            return (1. - d) / B;
    }

    double get_move_prob(size_t v, size_t r, size_t s, double c, double d,
                         bool reverse)
    {
        get_move_entries(v, _b[v], (reverse) ? r : s, _m_entries);
        return get_move_prob(v, r, s, c, d, reverse, _m_entries);
    }

    bool is_last(size_t v)
    {
        return _wr[_b[v]] == _vweight[v];
    }

    size_t node_weight(size_t v)
    {
        return _vweight[v];
    }

    // =========================================================================
    // Entropy computation
    // =========================================================================

    double get_deg_entropy(size_t v, const simple_degs_t&)
    {
        if (_ignore_degrees[v] == 1)
            return 0;
        auto kin = in_degreeS()(v, _g, _eweight);
        auto kout = out_degreeS()(v, _g, _eweight);
        if (_ignore_degrees[v] == 2)
            kout = 0;
        double S = -lgamma_fast(kin + 1) - lgamma_fast(kout + 1);
        return S * _vweight[v];
    }

    double get_deg_entropy(size_t v, typename degs_map_t::unchecked_t& degs)
    {
        if (_ignore_degrees[v] == 1)
            return 0;
        double S = 0;
        for (auto& ks : degs[v])
        {
            auto kin = get<0>(ks);
            auto kout = get<1>(ks);
            if (_ignore_degrees[v] == 2)
                kout = 0;
            int n = get<2>(ks);
            S -= n * (lgamma_fast(kin + 1) + lgamma_fast(kout + 1));
        }
        return S;
    }

    double sparse_entropy(bool multigraph, bool deg_entropy, bool exact)
    {
        double S = 0;

        if (exact)
        {
            for (auto e : edges_range(_bg))
                S += eterm_exact(source(e, _bg), target(e, _bg), _mrs[e], _bg);
            for (auto v : vertices_range(_bg))
                S += vterm_exact(_mrp[v], _mrm[v], _wr[v], _deg_corr, _bg);
        }
        else
        {
            for (auto e : edges_range(_bg))
                S += eterm(source(e, _bg), target(e, _bg), _mrs[e], _bg);
            for (auto v : vertices_range(_bg))
                S += vterm(_mrp[v], _mrm[v], _wr[v], _deg_corr, _bg);
        }

        if (_deg_corr && deg_entropy)
        {
            for (auto v : vertices_range(_g))
                S += get_deg_entropy(v, _degs);
        }

        if (multigraph)
            S += get_parallel_entropy();

        return S;
    }

    double dense_entropy(bool multigraph)
    {
        if (_deg_corr)
            throw GraphException("Dense entropy for degree corrected model not implemented!");
        double S = 0;
        for (auto e : edges_range(_bg))
        {
            auto r = source(e, _bg);
            auto s = target(e, _bg);
            S += eterm_dense(r, s, _mrs[e], _wr[r], _wr[s], multigraph, _bg);
        }
        return S;
    }

    double entropy(bool dense, bool multigraph, bool deg_entropy, bool exact,
                   bool recs, bool recs_dl, bool adjacency)
    {
        double S = 0;

        if (adjacency)
        {
            if (!dense)
                S = sparse_entropy(multigraph, deg_entropy, exact);
            else
                S = dense_entropy(multigraph);
        }

        if (recs)
        {
            for (size_t i = 0; i < _rec_types.size(); ++i)
            {
                auto& wp = _wparams[i];
                switch (_rec_types[i])
                {
                case weight_type::COUNT:
                    break;
                case weight_type::REAL_EXPONENTIAL:
                    for (auto me : edges_range(_bg))
                    {
                        auto ers = _brec[0][me];
                        auto xrs = _brec[i][me];
                        S += -positive_w_log_P(ers, xrs, wp[0], wp[1],
                                               _epsilon[i]);
                    }
                    if (recs_dl && std::isnan(wp[0]) && std::isnan(wp[1]))
                        S += -positive_w_log_P(_B_E, _recsum[i], wp[0], wp[1],
                                               _epsilon[i]);
                    break;
                case weight_type::DISCRETE_GEOMETRIC:
                    for (auto me : edges_range(_bg))
                    {
                        auto ers = _brec[0][me];
                        auto xrs = _brec[i][me];
                        S += -geometric_w_log_P(ers, xrs, wp[0], wp[1]);
                    }
                    if (recs_dl && std::isnan(wp[0]) && std::isnan(wp[1]))
                        S += -geometric_w_log_P(_B_E, _recsum[i], wp[0], wp[1]);
                    break;
                case weight_type::DISCRETE_POISSON:
                    for (auto me : edges_range(_bg))
                    {
                        auto ers = _brec[0][me];
                        auto xrs = _brec[i][me];
                        S += -poisson_w_log_P(ers, xrs, wp[0], wp[1]);
                    }
                    for (auto e : edges_range(_g))
                        S += lgamma(_rec[i][e] + 1);
                    if (recs_dl && std::isnan(wp[0]) && std::isnan(wp[1]))
                        S += -geometric_w_log_P(_B_E, _recsum[i], wp[0], wp[1]);
                    break;
                case weight_type::DISCRETE_BINOMIAL:
                    for (auto me : edges_range(_bg))
                    {
                        auto ers = _brec[0][me];
                        auto xrs = _brec[i][me];
                        S += -binomial_w_log_P(ers, xrs, wp[0], wp[1], wp[2]);
                    }
                    for (auto e : edges_range(_g))
                        S -= lbinom(wp[0], _rec[i][e]);
                    if (recs_dl && std::isnan(wp[1]) && std::isnan(wp[2]))
                        S += -geometric_w_log_P(_B_E, _recsum[i], wp[1], wp[2]);
                    break;
                case weight_type::REAL_NORMAL:
                    for (auto me : edges_range(_bg))
                    {
                        auto ers = _brec[0][me];
                        auto xrs = _brec[i][me];
                        auto x2rs = _bdrec[i][me];
                        S += -signed_w_log_P(ers, xrs, x2rs, wp[0], wp[1],
                                             wp[2], wp[3], _epsilon[i]);
                    }
                    if (std::isnan(wp[0]) && std::isnan(wp[1]))
                    {
                        if (recs_dl)
                            S += -signed_w_log_P(_B_E, _recsum[i], _recx2[i],
                                                 wp[0], wp[1], wp[2], wp[3],
                                                 _epsilon[i]);
                        S += -positive_w_log_P(_B_E_D, _recdx[i], wp[2],
                                               wp[3], _epsilon[i]);
                    }
                    break;
                case weight_type::DELTA_T: // waiting times
                    for (auto r : vertices_range(_bg))
                    {
                        if (_bignore_degrees[r] > 0)
                            S += -positive_w_log_P(_mrp[r], _brecsum[r], wp[0],
                                                   wp[1], _epsilon[i]);
                    }
                    break;
                }
            }
        }
        return S;
    }

    double get_partition_dl()
    {
        enable_partition_stats();
        double S = 0;
        for (auto& ps : _partition_stats)
            S += ps.get_partition_dl();
        return S;
    }

    double get_deg_dl(int kind)
    {
        enable_partition_stats();
        double S = 0;
        for (auto& ps : _partition_stats)
            S += ps.get_deg_dl(kind);
        return S;
    }

    double get_parallel_entropy()
    {
        double S = 0;
        for (auto v : vertices_range(_g))
        {
            gt_hash_map<decltype(v), size_t> us;
            for (auto e : out_edges_range(v, _g))
            {
                auto u = target(e, _g);
                if (u < v && !is_directed::apply<g_t>::type::value)
                    continue;
                us[u] += _eweight[e];
            }

            for (auto& uc : us)
            {
                auto& u = uc.first;
                auto& m = uc.second;
                if (m > 1)
                {
                    if (u == v && !is_directed::apply<g_t>::type::value)
                    {
                        assert(m % 2 == 0);
                        S += lgamma_fast(m/2 + 1) + m * log(2) / 2;
                    }
                    else
                    {
                        S += lgamma_fast(m + 1);
                    }
                }
            }
        }
        return S;
    }

    void enable_partition_stats()
    {
        if (_partition_stats.empty())
        {
            size_t E = 0;
            for (auto e : edges_range(_g))
                E += _eweight[e];
            size_t B = num_vertices(_bg);

            auto vi = std::max_element(vertices(_g).first, vertices(_g).second,
                                       [&](auto u, auto v)
                                       { return (this->_pclabel[u] <
                                                 this->_pclabel[v]); });
            size_t C = _pclabel[*vi] + 1;

            vector<vector<size_t>> vcs(C);
            vector<size_t> rc(num_vertices(_bg));
            for (auto v : vertices_range(_g))
            {
                vcs[_pclabel[v]].push_back(v);
                rc[_b[v]] = _pclabel[v];
            }

            for (size_t c = 0; c < C; ++c)
                _partition_stats.emplace_back(_g, _b, vcs[c], E, B,
                                              _vweight, _eweight, _degs,
                                              _ignore_degrees, _bmap,
                                              _allow_empty);

            for (auto r : vertices_range(_bg))
                _partition_stats[rc[r]].get_r(r);
        }
    }

    void disable_partition_stats()
    {
        _partition_stats.clear();
    }

    bool is_partition_stats_enabled() const
    {
        return !_partition_stats.empty();
    }

    partition_stats_t& get_partition_stats(size_t v)
    {
        return _partition_stats[_pclabel[v]];
    }

    void init_mcmc(double c, double dl)
    {
        if (!std::isinf(c))
        {
            if (_egroups.empty())
                _egroups.init(_b, _eweight, _g, _bg);
        }
        else
        {
            _egroups.clear();
        }

        if (dl)
            enable_partition_stats();
        else
            disable_partition_stats();
    }

    void couple_state(BlockStateVirtualBase& s, entropy_args_t ea)
    {
        _coupled_state = &s;
        _coupled_entropy_args = ea;
    }

    void decouple_state()
    {
        _coupled_state = nullptr;
    }

    void clear_egroups()
    {
        _egroups.clear();
    }

    void rebuild_neighbor_sampler()
    {
        _neighbor_sampler = neighbor_sampler_t(_g, _eweight);
    }

    void sync_emat()
    {
        _emat.sync(_bg);
    }

    size_t get_B_E()
    {
        return _B_E;
    }

    size_t get_B_E_D()
    {
        return _B_E_D;
    }

    size_t get_N()
    {
        size_t N = 0;
        for (auto r : vertices_range(_bg))
            N += _wr[r];
        return N;
    }

    bool check_edge_counts(bool emat=true)
    {
        gt_hash_map<std::pair<size_t, size_t>, size_t> mrs;
        for (auto e : edges_range(_g))
        {
            assert(std::max(source(e, _g),
                            target(e, _g)) < _b.get_storage().size());
            size_t r = _b[source(e, _g)];
            size_t s = _b[target(e, _g)];
            if (!is_directed::apply<g_t>::type::value && s < r)
                std::swap(r, s);
            mrs[std::make_pair(r, s)] += _eweight[e];
        }

        for (auto& rs_m : mrs)
        {
            auto r = rs_m.first.first;
            auto s = rs_m.first.second;
            size_t m_rs = 0;
            typename graph_traits<bg_t>::edge_descriptor me;
            if (emat)
            {
                me = _emat.get_me(r, s);
                if (me != _emat.get_null_edge())
                    m_rs = _mrs[me];
            }
            else
            {
                auto ret = boost::edge(r, s, _bg);
                me = ret.first;
                if (ret.second)
                    m_rs = _mrs[me];
            }
            if (m_rs != rs_m.second)
            {
                assert(false);
                return false;
            }
        }

        for (auto me : edges_range(_bg))
        {
            auto r = source(me, _bg);
            auto s = target(me, _bg);
            if (!is_directed::apply<g_t>::type::value && s < r)
                std::swap(r, s);
            auto m_rs = mrs[std::make_pair(r, s)];
            if (m_rs != size_t(_mrs[me]))
            {
                assert(false);
                return false;
            }
        }

        if (_coupled_state != nullptr)
            if (!_coupled_state->check_edge_counts(false))
            {
                assert(false);
                return false;
            }
        return true;
    }

    void check_node_counts()
    {
        vector<size_t> wr(num_vertices(_bg));
        for (auto v : vertices_range(_g))
            wr[_b[v]] += _vweight[v];

        for (auto r : vertices_range(_bg))
            assert(size_t(_wr[r]) == wr[r]);
    }

//private:
    typedef typename
        std::conditional<is_directed::apply<g_t>::type::value,
                         GraphInterface::multigraph_t,
                         undirected_adaptor<GraphInterface::multigraph_t>>::type
        bg_t;
    bg_t& _bg;

    typename mrs_t::checked_t _c_mrs;
    std::vector<typename rec_t::value_type::checked_t> _c_rec;
    std::vector<typename drec_t::value_type::checked_t> _c_drec;
    std::vector<typename brec_t::value_type::checked_t> _c_brec;
    std::vector<typename bdrec_t::value_type::checked_t> _c_bdrec;
    std::vector<double> _recsum;
    std::vector<double> _recx2;
    std::vector<double> _dBdx;
    size_t _B_E = 0;
    size_t _B_E_D = 0;
    int _rt = weight_type::NONE;

    typedef typename std::conditional<is_weighted_t::value,
                                      vmap_t::unchecked_t, vcmap_t>::type vweight_t;
    vweight_t _vweight;

    typedef typename std::conditional<is_weighted_t::value,
                                      emap_t::unchecked_t, ecmap_t>::type eweight_t;
    eweight_t _eweight;

    typedef typename std::conditional<is_weighted_t::value,
                                      degs_map_t::unchecked_t,
                                      simple_degs_t>::type degs_t;

    degs_t _degs;

    typedef typename std::conditional<use_hash_t::value,
                                      EHash<bg_t>,
                                      EMat<bg_t>>::type
        emat_t;
    emat_t _emat;

    EGroups<g_t, is_weighted_t> _egroups;
    bool _egroups_enabled = true;

    typedef NeighborSampler<g_t, is_weighted_t, boost::mpl::false_>
        neighbor_sampler_t;

    neighbor_sampler_t _neighbor_sampler;
    std::vector<partition_stats_t> _partition_stats;
    std::vector<size_t> _bmap;

    typedef EntrySet<g_t, bg_t, int, std::vector<double>,
                     std::vector<double>> m_entries_t;
    m_entries_t _m_entries;

    BlockStateVirtualBase* _coupled_state = nullptr;
    entropy_args_t _coupled_entropy_args;

    openmp_mutex _lock;
};

} // graph_tool namespace

#endif //GRAPH_BLOCKMODEL_HH
