extern "C" {

#include "afl-fuzz.h"
#include "patalog.h"

}

#include <map>
#include <vector>
#include <set>
#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <tuple>
#include <type_traits>
#include <iostream>

struct PataData {
  u32 var_id;
  u32 occur_id;
  std::vector<u8> lhs;
  std::vector<u8> rhs;
};

using PataDataSeq = std::vector<PataData>;
using PataSeqPerVar = std::map<u32, std::vector<const PataData*>>;
using UnstableVarTy = std::set<u32>;
using CricBytesTy = std::map<std::pair<u32, u32>, std::vector<std::pair<u32, u32>>>;

static u64 screen_update;

// #define PATA_DEBUG
// #define PATA_PROFILE

extern "C"
void afl_pata_on_queue_entry_destroy(struct queue_entry *q) {
  if (q->seq_per_var) {
    delete (PataSeqPerVar*)q->seq_per_var;
    q->seq_per_var = nullptr;
  }

  if (q->RVS) {
    delete (PataDataSeq*)q->RVS;
    q->RVS = nullptr;
  }

  if (q->unstable_var) {
    delete (UnstableVarTy*)q->unstable_var;
    q->unstable_var = nullptr;
  }

  if (q->critical_bytes) {
    delete (CricBytesTy*)q->critical_bytes;
    q->critical_bytes = nullptr;
  }

  if (q->solved) {
    delete (std::vector<u8>*)q->solved;
    q->solved = nullptr;
  }
}

extern "C"
void afl_pata_deinit(afl_state_t *afl) {
  if (afl->pata_metadata) {
    for (u32 i = 0; i < afl->num_pata_metadata_entries; ++i) {
      if (afl->pata_metadata[i].opaque) {
        ck_free(afl->pata_metadata[i].opaque);
        afl->pata_metadata[i].opaque = nullptr;
      }
      if (afl->pata_metadata[i].bf) {
        ck_free(afl->pata_metadata[i].bf);
        afl->pata_metadata[i].bf = nullptr;
      }
    }
    ck_free(afl->pata_metadata);
    afl->pata_metadata = nullptr;
  }
}

static u8
common_fuzz_patalog_stuff_filter_all(afl_state_t *afl, u8 *buf, u32 len) {
#ifdef PATA_PROFILE
  static u64 total_time = 0;
  static u64 total_execs = 0;
  u64 entry_time = get_cur_time_us();
#endif

  ((u32*)afl->shm.pata_map)[2] = PATA_FILTER_ALL;
  u8 ret = common_fuzz_patalog_stuff(afl, buf, len);

#ifdef PATA_PROFILE
  total_time += (get_cur_time_us() - entry_time);
  ++total_execs;
  if ((total_execs % 10000) == 0) {
    printf("common_fuzz_patalog_stuff_filter_all: avg exec time: %lld us\n", total_time / total_execs);
  }
#endif

  return ret;
}

static u8
common_fuzz_patalog_stuff_no_filter(afl_state_t *afl, u8 *buf, u32 len) {
#ifdef PATA_PROFILE
  static u64 total_time = 0;
  static u64 total_execs = 0;
  u64 entry_time = get_cur_time_us();
#endif

  ((u32*)afl->shm.pata_map)[2] = PATA_FILTER_NONE;
  u8 ret = common_fuzz_patalog_stuff(afl, buf, len);

#ifdef PATA_PROFILE
  total_time += (get_cur_time_us() - entry_time);
  ++total_execs;
  if ((total_execs % 10000) == 0) {
    printf("common_fuzz_patalog_stuff_no_filter: avg exec time: %lld us\n", total_time / total_execs);
  }
#endif

  return ret;
}

#ifdef PATA_DEBUG
static void dump_pata_metadata(afl_state_t *afl, u32 id) {
  const ConstraintVariable &cv = afl->pata_metadata[id];
  printf("###PATA Metadata #%d###\n", id);
  const char *kind[] = {"CMP", "SWITCH", "CALL"};
  printf("KIND: %s\n", kind[cv.kind]);
  switch (cv.kind) {
    case PATA_KIND_CMP: {
      printf("SIZE: %d\n", cv.size);
      printf("OP  : %d\n", cv.operation);
      printf("MISC: %d\n", cv.misc);
      break;
    }
    case PATA_KIND_SWITCH: {
      printf("SIZE: %d\n", cv.size);
      printf("CASES: %d", cv.operation);
      u32 num_cases = (cv.misc << 8) | cv.operation;
      u8 *cursor = (u8*)cv.opaque;
      for (u32 i = 0; i < num_cases; ++i) {
        switch (cv.size) {
          case 1: printf("0x%x, ", *((u8*)cursor)); break;
          case 2: printf("0x%x, ", *((u16*)cursor)); break;
          case 4: printf("0x%x, ", *((u32*)cursor)); break;
          case 8: printf("0x%llx, ", *((u64*)cursor)); break;
          default: FATAL("should not happen");
        }
        cursor += cv.size;
      }
      printf("\n");
      break;
    }
    case PATA_KIND_CALL: {
      printf("OP  : %d\n", cv.operation);
      break;
    }
    default: FATAL("should not happen");
  }
  fflush(stdout);
}
#endif

static void do_search(u8 *buf_begin, u8 *buf_end,
                      const std::vector<u8>::const_iterator &it_begin,
                      const std::vector<u8>::const_iterator &it_end,
                      std::vector<u8*> &res) {
  u8 *pos = buf_begin;
  while (true) {
    pos = std::search(pos, buf_end, it_begin, it_end);
    if (pos == buf_end) {
      break;
    }
    res.push_back(pos);
    pos += 1;
    if (pos == buf_end) {
      break;
    }
  }
}

static void do_search(u8 *buf_begin, u8 *buf_end,
                      const std::vector<u8>::const_reverse_iterator &it_begin,
                      const std::vector<u8>::const_reverse_iterator &it_end,
                      std::vector<u8*> &res) {
  u8 *pos = buf_begin;
  while (true) {
    pos = std::search(pos, buf_end, it_begin, it_end);
    if (pos == buf_end) {
      break;
    }
    res.push_back(pos);
    pos += 1;
    if (pos == buf_end) {
      break;
    }
  }
}

static void
get_seq_for_each_var(const PataDataSeq &RVS, PataSeqPerVar &seq) {
#ifdef PATA_PROFILE
  static u64 total_time = 0;
  static u64 total_execs = 0;
  u64 entry_time = get_cur_time_us();
#endif
  for (auto &ds : RVS) {
    if (seq.find(ds.var_id) == seq.end()) {
      seq[ds.var_id] = std::vector<const PataData*>({&ds});
    } else {
      seq[ds.var_id].push_back(&ds);
    }
  }
#ifdef PATA_PROFILE
  total_time += (get_cur_time_us() - entry_time);
  ++total_execs;
  if ((total_execs % 10000) == 0) {
    printf("get_seq_for_each_var: avg exec time: %lld us\n", total_time / total_execs);
  }
#endif
}

static void get_RVS_from_trace(afl_state_t *afl, PataDataSeq &RVS) {
  u32 num_records = *((u32*)afl->shm.pata_map);
  u8 *cursor = ((u8*)afl->shm.pata_map) + PATA_MAP_HEADER;
  u32 id;
  std::map<u32, u32> id_occur_map;
  PataData data;
  for (u32 i = 0; i < num_records; ++i) {
    id = *((u32*)cursor);
    cursor += sizeof(u32);
    const ConstraintVariable &cv = afl->pata_metadata[id];
    data.var_id = id;
    u32 occur_id;
    if (id_occur_map.find(id) == id_occur_map.end()) {
      occur_id = 0;
      id_occur_map[id] = 1;
    } else {
      occur_id = id_occur_map[id];
      id_occur_map[id] += 1;
    }
    data.occur_id = occur_id;
    switch(cv.kind) {
      case PATA_KIND_CMP: {
        data.lhs.assign(cursor, cursor + cv.size);
        cursor += cv.size;
        data.rhs.assign(cursor, cursor + cv.size);
        cursor += cv.size;
        break;
      }
      case PATA_KIND_SWITCH: {
        data.lhs.assign(cursor, cursor + cv.size);
        cursor += cv.size;
        break;
      }
      case PATA_KIND_CALL: {
        switch (cv.operation) {
          case PATA_CALL_MEMCMP: {
            u64 len = *((u64*)cursor);
            cursor += sizeof(u64);
            data.lhs.assign(cursor, cursor + len);
            cursor += len;
            data.rhs.assign(cursor, cursor + len);
            cursor += len;
            break;
          }
          case PATA_CALL_STRNCMP: {
            u64 len = *((u64*)cursor);
            cursor += sizeof(u64);
            data.lhs.assign(cursor, cursor + len);
            cursor += len;
            len = *((u64*)cursor);
            cursor += sizeof(u64);
            data.rhs.assign(cursor, cursor + len);
            cursor += len;
            break;
          }
          case PATA_CALL_STRCMP:
          case PATA_CALL_STRSTR:
          case PATA_CALL_MEMMEM: {
            u64 len = *((u64*)cursor);
            cursor += sizeof(u64);
            data.lhs.assign(cursor, cursor + len);
            cursor += len;
            len = *((u64*)cursor);
            cursor += sizeof(u64);
            data.rhs.assign(cursor, cursor + len);
            cursor += len;
            break;
          }
          default:
            FATAL("Unrecognized PATA_CALL Operation %d", cv.operation);
        }
        break;
      }
      default:
        FATAL("Unrecognized PATA KIND %d", cv.kind);
    }
    RVS.push_back(data);
  }
}

static void get_data_from_trace(afl_state_t *afl, const PataData &target,
                                PataData &ret) {
  u32 num_records = *((u32*)afl->shm.pata_map);
  u8 *cursor = ((u8*)afl->shm.pata_map) + PATA_MAP_HEADER;
  u32 id;
  u32 occur_num = 0;
  u64 len;
  bool do_log = false;
  const ConstraintVariable *cv;
  for (u32 i = 0; i < num_records; ++i) {
    id = *((u32*)cursor);
    cursor += sizeof(u32);
    cv = &afl->pata_metadata[id];
    if (id == target.var_id) {
      if (occur_num == target.occur_id) {
        do_log = true;
        ret.var_id = id;
        ret.occur_id = occur_num;
      } else {
        ++occur_num;
      }
    }
    switch(cv->kind) {
      case PATA_KIND_CMP: {
        if (do_log) {
          ret.lhs.assign(cursor, cursor + cv->size);
          cursor += cv->size;
          ret.rhs.assign(cursor, cursor + cv->size);
          return;
        }
        cursor += (2 * cv->size);
        break;
      }
      case PATA_KIND_SWITCH: {
        if (do_log) {
          ret.lhs.assign(cursor, cursor + cv->size);
          return;
        }
        cursor += cv->size;
        break;
      }
      case PATA_KIND_CALL: {
        switch (cv->operation) {
          case PATA_CALL_MEMCMP: {
            if (do_log) {
              len = *((u64*)cursor);
              cursor += sizeof(u64);
              ret.lhs.assign(cursor, cursor + len);
              cursor += len;
              ret.rhs.assign(cursor, cursor + len);
              return;
            }
            len = *((u64*)cursor);
            cursor += sizeof(u64);
            cursor += (2 * len);
            break;
          }
          case PATA_CALL_STRNCMP: {
            if (do_log) {
              len = *((u64*)cursor);
              cursor += sizeof(u64);
              ret.lhs.assign(cursor, cursor + len);
              cursor += len;
              len = *((u64*)cursor);
              cursor += sizeof(u64);
              ret.rhs.assign(cursor, cursor + len);
              return;
            }
            len = *((u64*)cursor);
            cursor += sizeof(u64);
            cursor += len;
            len = *((u64*)cursor);
            cursor += sizeof(u64);
            cursor += len;
            break;
          }
          case PATA_CALL_STRCMP:
          case PATA_CALL_STRSTR:
          case PATA_CALL_MEMMEM: {
            if (do_log) {
              len = *((u64*)cursor);
              cursor += sizeof(u64);
              ret.lhs.assign(cursor, cursor + len);
              cursor += len;
              len = *((u64*)cursor);
              cursor += sizeof(u64);
              ret.rhs.assign(cursor, cursor + len);
              return;
            }
            len = *((u64*)cursor);
            cursor += sizeof(u64);
            cursor += len;
            len = *((u64*)cursor);
            cursor += sizeof(u64);
            cursor += len;
            break;
          }
          default:
            FATAL("Unrecognized PATA_CALL Operation %d", cv->operation);
        }
        break;
      }
      default:
        FATAL("Unrecognized PATA KIND %d", cv->kind);
    }
  }
}



static u8 get_RVS(afl_state_t *afl, u8 *buf, u32 len, PataDataSeq &RVS) {
#ifdef PATA_PROFILE
  static u64 total_time = 0;
  static u64 total_execs = 0;
  u64 entry_time = get_cur_time_us();
#endif
  if (unlikely(common_fuzz_patalog_stuff_no_filter(afl, buf, len))) {
    return 1;
  }

  get_RVS_from_trace(afl, RVS);
#ifdef PATA_PROFILE
  total_time += (get_cur_time_us() - entry_time);
  ++total_execs;
  if ((total_execs % 10000) == 0) {
    printf("get_RVS: avg exec time: %lld us\n", total_time / total_execs);
  }
#endif
  return 0;
}

static u8
get_specific_pata_data(afl_state_t *afl, u8 *buf, u32 len,
                       const PataData &target, PataData &ret) {
#ifdef PATA_PROFILE
  static u64 total_time = 0;
  static u64 total_execs = 0;
  u64 entry_time = get_cur_time_us();
#endif
  // add filter
  ((u32*)afl->shm.pata_map)[2] = target.var_id;
  // then execute
  if (unlikely(common_fuzz_patalog_stuff(afl, buf, len))) {
    return 1;
  }

  get_data_from_trace(afl, target, ret);
#ifdef PATA_PROFILE
  total_time += (get_cur_time_us() - entry_time);
  ++total_execs;
  if ((total_execs % 10000) == 0) {
    printf("get_specific_pata_data: avg exec time: %lld us\n", total_time / total_execs);
  }
#endif
  return 0;
}


static u8 get_unstable_var(afl_state_t *afl, u8 *buf, u32 len,
                           UnstableVarTy &unstable_var,
                           const PataSeqPerVar &orig_seq) {
  PataDataSeq tmp_rvs;
  PataSeqPerVar seq;

#ifdef PATA_PROFILE
  static u64 total_time = 0;
  static u64 total_execs = 0;
  u64 entry_time = get_cur_time_us();
#endif
  
  for (u32 i = 0; i < CAL_CYCLES; ++i) {
    tmp_rvs.clear();
    if (unlikely(common_fuzz_patalog_stuff_no_filter(afl, buf, len))) {
      return 1;
    }
    if (*((u64*)afl->orig_pata_map) == *((u64*)afl->shm.pata_map)) {
      if (!memcmp(afl->orig_pata_map, afl->shm.pata_map, ((u32*)afl->shm.pata_map)[1])) {
        continue;
      }
    }
    get_RVS_from_trace(afl, tmp_rvs);

    seq.clear();
    get_seq_for_each_var(tmp_rvs, seq);
    // compare seq
    for (auto &v : orig_seq) {
      if (unstable_var.find(v.first) != unstable_var.end()) {
        continue;
      }
      auto seq_it = seq.find(v.first);
      if (seq_it == seq.end()) {
        // if the variable is not even shown, it's unstable
        unstable_var.insert(v.first);
      } else {
        // otherwise, let's compare the actual sequence
        auto seq_len = v.second.size();
        if (seq_len != seq_it->second.size()) {
          // unstable
          unstable_var.insert(v.first);
        } else {
          for (size_t j = 0; j < seq_len; ++j) {
            if (v.second[j]->lhs != seq_it->second[j]->lhs ||
                v.second[j]->rhs != seq_it->second[j]->rhs) {
              unstable_var.insert(v.first);
              break;
            }
          }
        }
      }
    }
  }
#ifdef PATA_PROFILE
  total_time += (get_cur_time_us() - entry_time);
  ++total_execs;
  if ((total_execs % 10000) == 0) {
    printf("get_unstable_var: avg exec time: %lld us\n", total_time / total_execs);
  }
#endif
  return 0;
}

static u8
collect_critical_bytes(afl_state_t *afl, u8 *buf, u32 len,
                       const UnstableVarTy &unstable_var,
                       const PataSeqPerVar &orig_seq,
                       CricBytesTy &cric_bytes) {
#define NUM_PERTURB   4
  
  u8 orig_byte;
  PataSeqPerVar seq;
  std::map<std::pair<u32, u32>, std::set<u32>> cric_bytes_tmp;
  PataDataSeq tmp_rvs;

  afl->stage_name = (u8*)"Critical Bytes";
  afl->stage_short = (u8*)"CB";
  afl->stage_max = len * NUM_PERTURB;
  afl->stage_cur = 0;

#ifdef PATA_PROFILE
  static u64 total_time = 0;
  static u64 total_execs = 0;
  u64 entry_time = get_cur_time_us();
#endif

  for (u32 offset = 0; offset < len; ++offset) {
    orig_byte = buf[offset];
    for (u32 perturb = 0; perturb < NUM_PERTURB; ++perturb) {
      switch (perturb) {
        case 0:
          // bit flipping
          buf[offset] ^= 0xFF;
          break;
        case 1:
          // increment by one
          buf[offset] += 1;
          break;
        case 2:
          buf[offset] -= 1;
          // decrement by one
          break;
        case 3:
          // interesting values
          buf[offset] = interesting_8[rand_below(afl, sizeof(interesting_8))];
          break;
      }
      // execute it, get RVS
      tmp_rvs.clear();
      if (unlikely(get_RVS(afl, buf, len, tmp_rvs))) {
        return 1;
      }
      // get seq for each var
      seq.clear();
      get_seq_for_each_var(tmp_rvs, seq);

      // then compare
      for (auto &v : orig_seq) {
        if (unstable_var.find(v.first) != unstable_var.end()) {
          continue;
        }
        auto seq_it = seq.find(v.first);
        if (seq_it != seq.end()) {
          auto len = MIN(v.second.size(), seq_it->second.size());
          for (size_t i = 0; i < len; ++i) {
            if (v.second[i]->lhs != seq_it->second[i]->lhs ||
                v.second[i]->rhs != seq_it->second[i]->rhs) {
              auto index = std::make_pair(v.first, i);
              if (cric_bytes_tmp.find(index) == cric_bytes_tmp.end()) {
                cric_bytes_tmp.insert(std::make_pair(index, std::set<u32>({offset})));
              } else {
                cric_bytes_tmp[index].insert(offset);
              }
            }
          }
        }
      }
      // recover the buffer
      buf[offset] = orig_byte;

      if (++afl->stage_cur % screen_update == 0) { show_stats(afl); }
    }
  }

  std::vector<std::pair<u32, u32>> sections;
  for (auto &index : cric_bytes_tmp) {
    sections.clear();
    std::vector<u32> cbytes_sorted(index.second.begin(), index.second.end());
    std::sort(cbytes_sorted.begin(), cbytes_sorted.end());
    
    auto num_offsets = cbytes_sorted.size();
    u32 last_offset = cbytes_sorted[0];
    u32 sec_len = 1;
    for (u32 i = 1; i < num_offsets; ++i) {
      if (cbytes_sorted[i] == cbytes_sorted[i - 1] + 1) {
        ++sec_len;
        continue;
      } else {
        sections.push_back(std::make_pair(last_offset, sec_len));
        last_offset = cbytes_sorted[i];
        sec_len = 1;
      }
    }
    sections.push_back(std::make_pair(last_offset, sec_len));
    cric_bytes[index.first] = sections;
  }

#ifdef PATA_PROFILE
  total_time += (get_cur_time_us() - entry_time);
  ++total_execs;
  if ((total_execs % 10) == 0) {
    printf("collect_critical_bytes: avg exec time: %lld us\n", total_time / total_execs);
  }
#endif

  return 0;
#undef NUM_PERTURB
}

static inline u8 is_meaningful_to_mutate(const PataData &data,
                                         const UnstableVarTy &unstable_var,
                                         u8 solved) {
  return (solved == 0) &&
         (unstable_var.find(data.var_id) == unstable_var.end());
}

// Success only when the variable is indeed a length.
static u8 length_explore(afl_state_t *afl, u8 *buf, u32 len,
                         const PataData &data,
                         const std::vector<u8> &orig_hit_cnt,
                         u8 &solved, bool &success) {
  u64 lhs_num, rhs_num;
  u8 *cursor;
  u64 num_cases;
  PataData new_data;
  const ConstraintVariable &cv = afl->pata_metadata[data.var_id];
  success = false;
  if (cv.kind == PATA_KIND_CALL) {
    return 0;
  }
  std::vector<u8> after_hit_cnt;

#ifdef PATA_PROFILE
  static u64 total_time = 0;
  static u64 total_execs = 0;
  u64 entry_time = get_cur_time_us();
#endif

  std::vector<u64> desired_len;
  if (cv.kind == PATA_KIND_CMP) {
    if (cv.misc == 2 && cv.operation >= 32) {
      lhs_num = 0;
      switch (cv.size) {
        case 1: lhs_num = *((u8*)data.lhs.data()); break;
        case 2: lhs_num = *((u16*)data.lhs.data()); break;
        case 4: lhs_num = *((u32*)data.lhs.data()); break;
        case 8: lhs_num = *((u64*)data.lhs.data()); break;
        default: FATAL("should not happen"); 
      }
      if (lhs_num != len) {
        return 0;
      }

      rhs_num = 0;
      switch (cv.size) {
        case 1: rhs_num = *((u8*)data.rhs.data()); break;
        case 2: rhs_num = *((u16*)data.rhs.data()); break;
        case 4: rhs_num = *((u32*)data.rhs.data()); break;
        case 8: rhs_num = *((u64*)data.rhs.data()); break;
        default: FATAL("should not happen"); 
      }
      if (rhs_num == 0) {
        return 0;
      }
      switch (cv.operation) {
        case 32: {
          if (lhs_num == rhs_num) {
            desired_len.push_back(rhs_num + 1);
            desired_len.push_back(rhs_num - 1);
          } else {
            desired_len.push_back(rhs_num);
          }
          break;
        }
        case 33: {
          if (lhs_num != rhs_num) {
            desired_len.push_back(rhs_num);
          } else {
            desired_len.push_back(rhs_num + 1);
            desired_len.push_back(rhs_num - 1);
          }
          break;
        }
        case 34:
        case 38: {
          if (lhs_num > rhs_num) {
            desired_len.push_back(rhs_num);
            desired_len.push_back(rhs_num - 1);
          } else {
            desired_len.push_back(rhs_num + 1);
          }
          break;
        }
        case 35:
        case 39: {
          if (lhs_num >= rhs_num) {
            desired_len.push_back(rhs_num - 1);
          } else {
            desired_len.push_back(rhs_num);
            desired_len.push_back(rhs_num + 1);
          }
          break;
        }
        case 36:
        case 40: {
          if (lhs_num < rhs_num) {
            desired_len.push_back(rhs_num);
            desired_len.push_back(rhs_num + 1);
          } else {
            desired_len.push_back(rhs_num - 1);
          }
          break;
        }
        case 37:
        case 41: {
          if (lhs_num <= rhs_num) {
            desired_len.push_back(rhs_num + 1);
          } else {
            desired_len.push_back(rhs_num - 1);
            desired_len.push_back(rhs_num);
          }
          break;
        }
      }
      
    }
  } else if (cv.kind == PATA_KIND_SWITCH) {
    lhs_num = 0;
    switch (cv.size) {
      case 1: lhs_num = *((u8*)data.lhs.data()); break;
      case 2: lhs_num = *((u16*)data.lhs.data()); break;
      case 4: lhs_num = *((u32*)data.lhs.data()); break;
      case 8: lhs_num = *((u64*)data.lhs.data()); break;
      default: FATAL("should not happen"); 
    }
    if (lhs_num != len) {
      return 0;
    }
    num_cases = (cv.misc << 8) | (cv.operation);
    cursor = (u8*)cv.opaque;
    for (u32 i = 0; i < num_cases; ++i) {
      switch (cv.size) {
        case 1: desired_len.push_back(*cursor); break;
        case 2: desired_len.push_back(*((u16*)cursor)); break;
        case 4: desired_len.push_back(*((u32*)cursor)); break;
        case 8: desired_len.push_back(*((u64*)cursor)); break;
        default: FATAL("should not happen");
      }
      cursor += cv.size;
    }
  }

  if (desired_len.empty()) {
    return 0;
  }

  u64 orig_entries, new_entries, num_execs;
  orig_entries = afl->queued_items + afl->saved_crashes;
  num_execs = 0;
  
  for (auto dl : desired_len) {
    if (dl == len) {
      continue;
    }
    if (dl > len) {
      if (dl > MAX_FILE) {
        continue;
      }
      u8 *new_buf = (u8*)ck_alloc(dl);
      memcpy(new_buf, buf, len);

      // Is this real length?
      new_data.var_id = 0xFFFFFFFF;
      if (unlikely(get_specific_pata_data(afl, new_buf, dl, data, new_data))) {
        ck_free(new_buf);
        success = false;
        return 1;
      }
      if (new_data.var_id != data.var_id) {
        ck_free(new_buf);
        continue;
      }
      lhs_num = 0;
      switch (cv.size) {
        case 1: lhs_num = *((u8*)data.lhs.data()); break;
        case 2: lhs_num = *((u16*)data.lhs.data()); break;
        case 4: lhs_num = *((u32*)data.lhs.data()); break;
        case 8: lhs_num = *((u64*)data.lhs.data()); break;
        default: FATAL("should not happen"); 
      }
      if (lhs_num != dl) {
        ck_free(new_buf);
        continue;
      }

      success = true;
      // branch solved?
      for (u32 i = 0; i < cv.num_bf; ++i) {
        after_hit_cnt.push_back(afl->fsrv.trace_bits[cv.bf[i]]);
      }
      if (after_hit_cnt != orig_hit_cnt) {
        solved = 1;
      }
      after_hit_cnt.clear();

      if (unlikely(common_fuzz_stuff(afl, new_buf, dl))) {
        ck_free(new_buf);
        success = false;
        return 1;
      }
      ck_free(new_buf);
      ++num_execs;
    } else {
      // Is this real length?
      new_data.var_id = 0xFFFFFFFF;
      if(unlikely(get_specific_pata_data(afl, buf, dl, data, new_data))) {
        success = false;
        return 1;
      }
      if (new_data.var_id != data.var_id) {
        continue;
      }

      lhs_num = 0;
      switch (cv.size) {
        case 1: lhs_num = *((u8*)data.lhs.data()); break;
        case 2: lhs_num = *((u16*)data.lhs.data()); break;
        case 4: lhs_num = *((u32*)data.lhs.data()); break;
        case 8: lhs_num = *((u64*)data.lhs.data()); break;
        default: FATAL("should not happen"); 
      }
      if (lhs_num != dl) {
        continue;
      }

      success = true;
      // branch solved?
      for (u32 i = 0; i < cv.num_bf; ++i) {
        after_hit_cnt.push_back(afl->fsrv.trace_bits[cv.bf[i]]);
      }
      if (after_hit_cnt != orig_hit_cnt) {
        solved = 1;
      }
      after_hit_cnt.clear();

      if (unlikely(common_fuzz_stuff(afl, buf, dl))) {
        success = false;
        return 1;
      }
      ++num_execs;
    }
  }

  new_entries = afl->queued_items + afl->saved_crashes;
  afl->stage_finds[STAGE_LENGTH_EXPLORE] += new_entries - orig_entries;
  afl->stage_cycles[STAGE_LENGTH_EXPLORE] += num_execs;

#ifdef PATA_PROFILE
  total_time += (get_cur_time_us() - entry_time);
  ++total_execs;
  if ((total_execs % 10) == 0) {
    printf("length_explore: avg exec time: %lld us\n", total_time / total_execs);
  }
#endif

  return 0;
}

template<typename T> inline static T
calc_gap_for_cmp(const PataData &data) {
  T lhs = *((T*)data.lhs.data());
  T rhs = *((T*)data.rhs.data());
  if constexpr(std::is_integral<T>()) {
    return lhs >= rhs ? lhs - rhs : rhs - lhs;
  } else {
    return std::abs(lhs - rhs);
  }
}

template<typename T> inline static T
calc_gap_for_switch(const PataData &data, T case_value) {
  T lhs = *((T*)data.lhs.data());
  return lhs >= case_value ? lhs - case_value : case_value - lhs;
}


// signed integer
template<typename T> inline static bool
eval_constraint_sicmp(const ConstraintVariable &cv, const PataData &data) {
  T lhs = *((T*)data.lhs.data());
  T rhs = *((T*)data.rhs.data());

  switch (cv.operation) {
    case 38: return lhs > rhs;
    case 39: return lhs >= rhs;
    case 40: return lhs < rhs;
    case 41: return lhs <= rhs;
    default: FATAL("should not happen");
  }
}

// unsigned integer
template<typename T> inline static bool
eval_constraint_uicmp(const ConstraintVariable &cv, const PataData &data) {
  T lhs = *((T*)data.lhs.data());
  T rhs = *((T*)data.rhs.data());

  switch (cv.operation) {
    case 32: return lhs == rhs;
    case 33: return lhs != rhs;
    case 34: return lhs > rhs;
    case 35: return lhs >= rhs;
    case 36: return lhs < rhs;
    case 37: return lhs <= rhs;
    default: FATAL("should not happen");
  }
}

template<typename T> inline static bool
eval_constraint_fcmp(const ConstraintVariable &cv, const PataData &data) {
  T lhs = *((T*)data.lhs.data());
  T rhs = *((T*)data.rhs.data());
  bool ordered = std::isnan(lhs) && std::isnan(rhs);

  switch (cv.operation) {
    case 0: return false;
    case 1: return ordered && lhs == rhs;
    case 2: return ordered && lhs > rhs;
    case 3: return ordered && lhs >= rhs;
    case 4: return ordered && lhs < rhs;
    case 5: return ordered && lhs <= rhs;
    case 6: return ordered && lhs != rhs;
    case 7: return ordered;
    case 8: return !ordered;
    case 9: return (!ordered) || lhs == rhs;
    case 10: return (!ordered) || lhs > rhs;
    case 11: return (!ordered) || lhs >= rhs;
    case 12: return (!ordered) || lhs < rhs;
    case 13: return (!ordered) || lhs <= rhs;
    case 14: return (!ordered) || lhs != rhs;
    case 15: return true;
    default: FATAL("should not happen");
  }
}

template<typename T> struct to_signed { };

template<> struct to_signed<u8> { using ty = s8; };
template<> struct to_signed<u16> { using ty = s16; };
template<> struct to_signed<u32> { using ty = s32; };
template<> struct to_signed<u64> { using ty = s64; };

template<typename T> static inline bool
eval_constraint_cmp(const ConstraintVariable &cv, const PataData &data) {
  if constexpr(std::is_integral<T>()) {
    // determine type
    if (cv.operation <= 37) {
      // unsigned
      return eval_constraint_uicmp<T>(cv, data);
    } else {
      // signed, conversion first
      return eval_constraint_sicmp<typename to_signed<T>::ty>(cv, data);
    }
  } else {
    return eval_constraint_fcmp<T>(cv, data);
  }
}

template<typename T> static inline bool
eval_constraint_switch(const PataData &data, T case_value) {
  return (*((T*)data.lhs.data()) == case_value);
}

template<typename T> static u8
calc_expected_value_for_fcmp(const ConstraintVariable &cv,
                             std::vector<std::vector<u8>> &lhs_expected,
                             const PataData &data, bool reverse) {
  if (cv.operation == 0 || cv.operation == 15) {
    return 0;
  }

#ifdef PATA_PROFILE
  static u64 total_time = 0;
  static u64 total_execs = 0;
  u64 entry_time = get_cur_time_us();
#endif

  T rhs, lhs;
  if (!reverse) {
    rhs = *((T*)data.rhs.data());
    lhs = *((T*)data.lhs.data());
  } else {
    rhs = *((T*)data.lhs.data());
    lhs = *((T*)data.rhs.data());
  }
  if (std::isnan(rhs)) { return 0; }
  bool lhs_nan = std::isnan(lhs);
  const T nan = std::numeric_limits<T>::quiet_NaN();
  T tmp;
  u8 real_op = cv.operation;
  if (reverse) {
    switch (cv.operation) {
      case 2: real_op = 4; break;
      case 3: real_op = 5; break;
      case 4: real_op = 2; break;
      case 5: real_op = 3; break;
      case 10: real_op = 12; break;
      case 11: real_op = 13; break;
      case 12: real_op = 10; break;
      case 13: real_op = 11; break;
      default: break;
    }
  }
  switch (real_op) {
    case 1: {
      if (rhs == lhs) {
        tmp = rhs + 1.0;
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
        tmp = rhs - 1.0;
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
      } else {
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&rhs)), ((u8*)(&rhs)) + sizeof(T)));
      }
      break;
    }
    /* FCMP_OGT */
    case 2: {
      tmp = rhs - 1.0;
      if (lhs > rhs) {
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&rhs)), ((u8*)(&rhs)) + sizeof(T)));
      } else {
        tmp = rhs + 1.0;
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
      }
      break;
    }
    /* FCMP_OGE */
    case 3: {
      tmp = rhs - 1.0;
      if (lhs >= rhs) {
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
      } else {
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&rhs)), ((u8*)(&rhs)) + sizeof(T)));
        tmp = rhs + 1.0;
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
      }
      break;
    }
    /* FCMP_OLT */
    case 4: {
      tmp = rhs + 1.0;
      if (lhs < rhs) {
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&rhs)), ((u8*)(&rhs)) + sizeof(T)));
      } else {
        tmp = rhs - 1.0;
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
      }
      break;
    }
    /* FCMP_OLE */
    case 5: {
      tmp = rhs + 1.0;
      if (lhs <= rhs) {
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
      } else {
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&rhs)), ((u8*)(&rhs)) + sizeof(T)));
        tmp = rhs - 1.0;
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
      }
      break;
    }
    /* FCMP_ONE */
    case 6: {
      if (rhs != lhs) {
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&rhs)), ((u8*)(&rhs)) + sizeof(T)));
      } else {
        tmp = rhs + 1.0;
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
        tmp = rhs - 1.0;
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
      }
      break;
    }
    /* FCMP_ORD */
    case 7: {
      lhs_expected.push_back(
        std::vector<u8>(((u8*)(&rhs)), ((u8*)(&rhs)) + sizeof(T)));
      break;
    }
    /* FCMP_UNO */
    case 8: {
      if (lhs_nan) {
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&rhs)), ((u8*)(&rhs)) + sizeof(T)));
      } else {
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&nan)), ((u8*)(&nan)) + sizeof(T)));
      }
      break;
    }
    /* FCMP_UEQ */
    case 9: {
      tmp = rhs + 1.0;
      if (lhs_nan) {
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
      } else {
        if (lhs == rhs) {
          lhs_expected.push_back(
            std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
          lhs_expected.push_back(
            std::vector<u8>(((u8*)(&nan)), ((u8*)(&nan)) + sizeof(T)));
        } else {
          lhs_expected.push_back(
            std::vector<u8>(((u8*)(&rhs)), ((u8*)(&rhs)) + sizeof(T)));
          lhs_expected.push_back(
            std::vector<u8>(((u8*)(&nan)), ((u8*)(&nan)) + sizeof(T)));
        }
      }
      break;
    }
    /* FCMP_UGT */
    case 10: {
      tmp = rhs - 1.0;
      if (lhs_nan) {
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
      } else {
        if (lhs > rhs) {
          lhs_expected.push_back(
            std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
          lhs_expected.push_back(
            std::vector<u8>(((u8*)(&nan)), ((u8*)(&nan)) + sizeof(T)));
        } else {
          tmp = rhs + 1.0;
          lhs_expected.push_back(
            std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
          lhs_expected.push_back(
            std::vector<u8>(((u8*)(&nan)), ((u8*)(&nan)) + sizeof(T)));
        }
      }
      break;
    }
    /* FCMP_UGE */
    case 11: {
      tmp = rhs - 1.0;
      if (lhs_nan) {
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
      } else {
        if (lhs >= rhs) {
          lhs_expected.push_back(
            std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
          lhs_expected.push_back(
            std::vector<u8>(((u8*)(&nan)), ((u8*)(&nan)) + sizeof(T)));
        } else {
          tmp = rhs + 1.0;
          lhs_expected.push_back(
            std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
          lhs_expected.push_back(
            std::vector<u8>(((u8*)(&nan)), ((u8*)(&nan)) + sizeof(T)));
        }
      }
      break;
    }
    /* FCMP_ULT */
    case 12: {
      tmp = rhs + 1.0;
      if (lhs_nan) {
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
      } else {
        if (lhs < rhs) {
          lhs_expected.push_back(
            std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
          lhs_expected.push_back(
            std::vector<u8>(((u8*)(&nan)), ((u8*)(&nan)) + sizeof(T)));
        } else {
          tmp = rhs - 1.0;
          lhs_expected.push_back(
            std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
          lhs_expected.push_back(
            std::vector<u8>(((u8*)(&nan)), ((u8*)(&nan)) + sizeof(T)));
        }
      }
      break;
    }
    /* FCMP_ULE */
    case 13: {
      tmp = rhs + 1.0;
      if (lhs_nan) {
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
      } else {
        if (lhs <= rhs) {
          lhs_expected.push_back(
            std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
          lhs_expected.push_back(
            std::vector<u8>(((u8*)(&nan)), ((u8*)(&nan)) + sizeof(T)));
        } else {
          tmp = rhs - 1.0;
          lhs_expected.push_back(
            std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
          lhs_expected.push_back(
            std::vector<u8>(((u8*)(&nan)), ((u8*)(&nan)) + sizeof(T)));
        }
      }
      break;
    }
    /* FCMP_UNE */
    case 14: {
      if (lhs_nan) {
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&rhs)), ((u8*)(&rhs)) + sizeof(T)));
      } else {
        if (lhs != rhs) {
          lhs_expected.push_back(
            std::vector<u8>(((u8*)(&rhs)), ((u8*)(&rhs)) + sizeof(T)));
          lhs_expected.push_back(
            std::vector<u8>(((u8*)(&nan)), ((u8*)(&nan)) + sizeof(T)));
        } else {
          tmp = rhs - 1.0;
          lhs_expected.push_back(
            std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
          lhs_expected.push_back(
            std::vector<u8>(((u8*)(&nan)), ((u8*)(&nan)) + sizeof(T)));
        }
      }
      break;
    }
  }

#ifdef PATA_PROFILE
  total_time += (get_cur_time_us() - entry_time);
  ++total_execs;
  if ((total_execs % 100) == 0) {
    printf("calc_expected_value_for_fcmp: avg exec time: %lld us\n", total_time / total_execs);
  }
#endif

  return 1;
}

template<typename T> static u8
calc_expected_value_for_icmp(const ConstraintVariable &cv,
                             std::vector<std::vector<u8>> &lhs_expected,
                             const PataData &data, bool reverse) {

#ifdef PATA_PROFILE
  static u64 total_time = 0;
  static u64 total_execs = 0;
  u64 entry_time = get_cur_time_us();
#endif

  T rhs, lhs;
  if (!reverse) {
    rhs = *((T*)data.rhs.data());
    lhs = *((T*)data.lhs.data());
  } else {
    rhs = *((T*)data.lhs.data());
    lhs = *((T*)data.rhs.data());
  }
  T tmp;

  u8 real_op = cv.operation;
  if (reverse) {
    switch (cv.operation) {
      case 34: real_op = 36; break;
      case 35: real_op = 37; break;
      case 36: real_op = 34; break;
      case 37: real_op = 35; break;
      case 38: real_op = 40; break;
      case 39: real_op = 41; break;
      case 40: real_op = 38; break;
      case 41: real_op = 39; break;
      default: break;
    }
  }

  switch (real_op) {
    /* ICMP_EQ */
    case 32: {
      if (lhs == rhs) {
        tmp = rhs + 1;
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
        tmp = rhs - 1;
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
      } else {
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&rhs)), ((u8*)(&rhs)) + sizeof(T)));
      }
      break;
    }
    /* ICMP_NE */
    case 33: {
      if (lhs != rhs) {
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&rhs)), ((u8*)(&rhs)) + sizeof(T)));
      } else {
        tmp = rhs + 1;
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
        tmp = rhs - 1;
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
      }
      break;
    }
    /* ICMP_UGT, ICMP_SGT */
    case 34:
    case 38: {
      if (lhs > rhs) {
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&rhs)), ((u8*)(&rhs)) + sizeof(T)));
        tmp = rhs - 1;
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
      } else {
        tmp = rhs + 1;
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
      }
      break;
    }
    /* ICMP_UGE, ICMP_SGE */
    case 35:
    case 39: {
      if (lhs >= rhs) {
        tmp = rhs - 1;
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
      } else {
        tmp = rhs + 1;
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&rhs)), ((u8*)(&rhs)) + sizeof(T)));
      }
      break;
    }
    /* ICMP_ULT, ICMP_SLT */
    case 36:
    case 40: {
      if (lhs < rhs) {
        tmp = rhs + 1;
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&rhs)), ((u8*)(&rhs)) + sizeof(T)));
      } else {
        tmp = rhs - 1;
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
      }
      break;
    }
    /* ICMP_ULE, ICMP_SLE */
    case 37:
    case 41: {
      if (lhs <= rhs) {
        tmp = rhs + 1;
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
      } else {
        tmp = rhs - 1;
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&tmp)), ((u8*)(&tmp)) + sizeof(T)));
        lhs_expected.push_back(
          std::vector<u8>(((u8*)(&rhs)), ((u8*)(&rhs)) + sizeof(T)));
      }
      break;
    }
    default: FATAL("should not happen");
  }

#ifdef PATA_PROFILE
  total_time += (get_cur_time_us() - entry_time);
  ++total_execs;
  if ((total_execs % 100) == 0) {
    printf("calc_expected_value_for_icmp: avg exec time: %lld us\n", total_time / total_execs);
  }
#endif

  return 1;
}


static u8
calc_expected_value_for_cmp(const ConstraintVariable &cv,
                            std::vector<std::vector<u8>> &lhs_expected,
                            const PataData &data, bool reverse) {
  if (cv.operation <= 15) {
    // FP
    if (cv.size == 4) {
      return calc_expected_value_for_fcmp<float>(cv, lhs_expected, data, reverse);
    } else if (cv.size == 8) {
      return calc_expected_value_for_fcmp<double>(cv, lhs_expected, data, reverse);
    } else {
      return 0;
    }
  } else if (cv.operation >= 32) {
    switch (cv.size) {
      case 1: return calc_expected_value_for_icmp<u8>(cv, lhs_expected, data, reverse);
      case 2: return calc_expected_value_for_icmp<u16>(cv, lhs_expected, data, reverse);
      case 4: return calc_expected_value_for_icmp<u32>(cv, lhs_expected, data, reverse);
      case 8: return calc_expected_value_for_icmp<u64>(cv, lhs_expected, data, reverse);
      default: FATAL("should not happen");
    }
  } else {
    return 0;
  }
}

static void
calc_expected_value_for_switch(const ConstraintVariable &cv,
                               std::vector<std::vector<u8>> &lhs_expected) {
  u32 num_cases = (cv.misc << 8 | cv.operation);
  u8 *cursor = (u8*)cv.opaque;
  for (u32 i = 0; i < num_cases; ++i) {
    lhs_expected.push_back(std::vector<u8>(cursor, cursor + cv.size));
    cursor += cv.size;
  }
}

static u8
calc_expected_value_for_call(const ConstraintVariable &cv,
                             std::vector<std::vector<u8>> &lhs_expected,
                             const PataData &data, bool reverse) {
  const std::vector<u8> &rhs = reverse ? data.lhs : data.rhs;
  // const std::vector<u8> &lhs = reverse ? data.rhs : data.lhs;

  if (rhs.empty()) {
    return 0;
  }

  std::vector<u8> tmp = rhs;

  switch (cv.operation) {
    case PATA_CALL_MEMCMP:
    case PATA_CALL_STRNCMP:
    case PATA_CALL_STRCMP: {
      lhs_expected.push_back(rhs);
      tmp[0] = rhs[0] - 1;
      lhs_expected.push_back(tmp);
      tmp[0] = rhs[0] + 1;
      lhs_expected.push_back(tmp);
      break;
    }
    case PATA_CALL_STRSTR:
    case PATA_CALL_MEMMEM: {
      lhs_expected.push_back(tmp);
      break;
    }
    default: FATAL("should not happen");
  }

  return 1;
}

// Success only when the variable is indeed a direct copy.
static u8 copy_explore(afl_state_t *afl, u8 *orig_buf, u8 *buf, u32 len,
                       const PataData &data,
                       const std::vector<std::pair<u32, u32>> &cbytes,
                       const std::vector<u8> &orig_hit_cnt,
                       u8 &solved, bool &success) {

#ifdef PATA_PROFILE
  static u64 total_time = 0;
  static u64 total_execs = 0;
  u64 entry_time = get_cur_time_us();
#endif

  auto &cv = afl->pata_metadata[data.var_id];
  success = false;

  const std::vector<std::pair<u32, u32>> &sections = cbytes;

  // 3. try to find byte sequence
  std::vector<std::pair<u32, u32>> lhs_pos;
  std::vector<std::pair<u32, u32>> rhs_pos;
  std::vector<std::vector<u8>> lhs_expected;
  std::vector<std::vector<u8>> rhs_expected;
  std::vector<u8*> res;
  u8 *buf_begin, *buf_end;
  bool lhs_le = true;
  bool rhs_le = true;
  std::vector<u8> after_hit_cnt;

  // identify
  switch (cv.kind) {
    case PATA_KIND_CMP: {
      // identify
      for (auto &sec : sections) {
        buf_begin = buf + sec.first;
        buf_end = buf + sec.first + sec.second;
        // Deal with LHS
        do_search(buf_begin, buf_end, data.lhs.begin(), data.lhs.end(), res);
        if (res.empty()) {
          do_search(buf_begin, buf_end, data.lhs.rbegin(), data.lhs.rend(), res);
          if (!res.empty()) {
            lhs_le = false;
          }
        }
        for (auto r : res) {
          lhs_pos.push_back(std::make_pair(r - buf, data.lhs.size()));
        }

        if (cv.misc == 0) {
          // Deal with RHS
          do_search(buf_begin, buf_end, data.rhs.begin(), data.rhs.end(), res);
          if (res.empty()) {
            do_search(buf_begin, buf_end, data.rhs.rbegin(), data.rhs.rend(), res);
            if (!res.empty()) {
              rhs_le = false;
            }
          }
          for (auto r : res) {
            rhs_pos.push_back(std::make_pair(r - buf, data.rhs.size()));
          }
        }
      }
      break;
    }
    case PATA_KIND_SWITCH: {
      for (auto &sec : sections) {
        buf_begin = buf + sec.first;
        buf_end = buf + sec.first + sec.second;

        do_search(buf_begin, buf_end, data.lhs.begin(), data.lhs.end(), res);
        if (res.empty()) {
          do_search(buf_begin, buf_end, data.lhs.rbegin(), data.lhs.rend(), res);
          if (!res.empty()) {
            lhs_le = false;
          }
        }
        for (auto r : res) {
          lhs_pos.push_back(std::make_pair(r - buf, data.lhs.size()));
        }
      }
      break;
    }
    case PATA_KIND_CALL: {
      for (auto &sec : sections) {
        buf_begin = buf + sec.first;
        buf_end = buf + sec.first + sec.second;
        do_search(buf_begin, buf_end, data.lhs.begin(), data.lhs.end(), res);
        if (res.empty()) {
          do_search(buf_begin, buf_end, data.lhs.rbegin(), data.lhs.rend(), res);
          if (!res.empty()) {
            lhs_le = false;
          }
        }
        for (auto r : res) {
          lhs_pos.push_back(std::make_pair(r - buf, data.lhs.size()));
        }

        do_search(buf_begin, buf_end, data.rhs.begin(), data.rhs.end(), res);
        if (res.empty()) {
          do_search(buf_begin, buf_end, data.rhs.rbegin(), data.rhs.rend(), res);
          if (!res.empty()) {
            rhs_le = false;
          }
        }
        for (auto r : res) {
          rhs_pos.push_back(std::make_pair(r - buf, data.rhs.size()));
        }
      }
      break;
    }
    default: FATAL("should not happen");
  }

  // calculate expected value
  switch (cv.kind) {
    case PATA_KIND_CMP: {
      // calculate expected value & patching
      if (cv.misc == 2 && !lhs_pos.empty()) {
        // RHS is a constant, LHS is a direct copy
        if (calc_expected_value_for_cmp(cv, lhs_expected, data, false) == 0) {
          return 0;
        }
      } else if (cv.misc == 0 && !lhs_pos.empty() && !rhs_pos.empty()) {
        // Both RHS and LHS are direct copies
        if (calc_expected_value_for_cmp(cv, lhs_expected, data, false) == 0) {
          return 0;
        }
      } else if (cv.misc == 0 && (!lhs_pos.empty() || !rhs_pos.empty())) {
        // One of RHS and LHS is direct copy
        if (rhs_pos.empty()) {
          // LHS is direct copy
          if (calc_expected_value_for_cmp(cv, lhs_expected, data, false) == 0) {
            return 0;
          }
        } else {
          // RHS is direct copy
          if (calc_expected_value_for_cmp(cv, rhs_expected, data, true) == 0) {
            return 0;
          }
        }
      } else {
        return 0;
      }
      break;
    }
    case PATA_KIND_SWITCH: {
      if (lhs_pos.empty()) {
        return 0;
      }
      // Direct copy
      calc_expected_value_for_switch(cv, lhs_expected);
      break;
    }
    case PATA_KIND_CALL: {
      if (lhs_pos.empty() && rhs_pos.empty()) {
        return 0;
      }
      if (!lhs_pos.empty()) {
        if (calc_expected_value_for_call(cv, lhs_expected, data, false) == 0) {
          return 0;
        }
      }
      if (!rhs_pos.empty()) {
        if (calc_expected_value_for_call(cv, rhs_expected, data, true) == 0) {
          return 0;
        }
      }
      break;
    }
    default: FATAL("should not happen");
  }

  // patching
  bool patch_lhs = !lhs_expected.empty();
  std::vector<std::vector<u8>> &expected = patch_lhs ? lhs_expected : rhs_expected;
  std::vector<std::pair<u32, u32>> &pos = patch_lhs ? lhs_pos : rhs_pos;
  bool le = patch_lhs ? lhs_le : rhs_le;
  u32 new_size;
  u8 *tmp, *cursor;
  PataData new_data;

  u64 orig_entries, new_entries, num_execs;
  orig_entries = afl->queued_items + afl->saved_crashes;
  num_execs = 0;

  if (!expected.empty()) {
    // do patch
    for (auto &pb : expected) {
      for (auto &pp : pos) {
        if (pb.size() == pp.second) {
          if (le) {
            memcpy(buf + pp.first, pb.data(), pp.second);
          } else {
            std::copy(pb.rbegin(), pb.rend(), buf + pp.first);
          }

          // is direct copy? 
          if (unlikely(get_specific_pata_data(afl, buf, len, data, new_data))) {
            success = false;
            return 1;
          }
          if (new_data.var_id != data.var_id) {
            continue;
          }

          std::vector<u8> &patched_data = patch_lhs ? new_data.lhs : new_data.rhs;
          if (le) {
            success = (patched_data == pb);
          } else {
            success = (std::equal(pb.begin(), pb.end(), patched_data.rbegin()));
          }
          
          // solved?
          for (u32 i = 0; i < cv.num_bf; ++i) {
            after_hit_cnt.push_back(afl->fsrv.trace_bits[cv.bf[i]]);
          }
          if (after_hit_cnt != orig_hit_cnt) {
            solved = 1;
          }
          after_hit_cnt.clear();
          
          if (unlikely(common_fuzz_stuff(afl, buf, len))) {
            success = false;
            return 1;
          }
          memcpy(buf, orig_buf, len);
          ++num_execs;
        } else {
          new_size = len + (pb.size() - pp.second);
          if (new_size > MAX_FILE) {
            continue;
          }
          tmp = (u8*)ck_alloc(new_size);
          cursor = tmp;
          memcpy(cursor, buf, pp.first);
          cursor += pp.first;
          if (le) {
            memcpy(cursor, pb.data(), pb.size());
          } else {
            std::copy(pb.rbegin(), pb.rend(), cursor);
          }
          cursor += pb.size();
          memcpy(cursor, buf + pp.first + pp.second, len - pp.first - pp.second);

          // is direct copy? 
          if (unlikely(get_specific_pata_data(afl, tmp, new_size, data, new_data))) {
            ck_free(tmp);
            success = false;
            return 1;
          }

          if (new_data.var_id != data.var_id) {
            ck_free(tmp);
            continue;
          }

          std::vector<u8> &patched_data = patch_lhs ? new_data.lhs : new_data.rhs;
          if (le) {
            success = (patched_data == pb);
          } else {
            success = (std::equal(pb.begin(), pb.end(), patched_data.rbegin()));
          }

          // solved?
          for (u32 i = 0; i < cv.num_bf; ++i) {
            after_hit_cnt.push_back(afl->fsrv.trace_bits[cv.bf[i]]);
          }
          if (after_hit_cnt != orig_hit_cnt) {
            solved = 1;
          }
          after_hit_cnt.clear();

          if (unlikely(common_fuzz_stuff(afl, tmp, new_size))) {
            success = false;
            ck_free(tmp);
            return 1;
          }
          ck_free(tmp);
          ++num_execs;
        }
      }
    }
  }

  new_entries = afl->queued_items + afl->saved_crashes;
  afl->stage_finds[STAGE_COPY_EXPLORE] += new_entries - orig_entries;
  afl->stage_cycles[STAGE_COPY_EXPLORE] += ++num_execs;

#ifdef PATA_PROFILE
  total_time += (get_cur_time_us() - entry_time);
  ++total_execs;
  if ((total_execs % 100) == 0) {
    printf("copy_explore: avg exec time: %lld us\n", total_time / total_execs);
  }
#endif
  return 0;
}

template<typename T> static u8
calc_move_operation_cmp(afl_state_t *afl, u8 *buf, u32 len, u32 offset,
                    T orig_gap, const PataData &data, PataData &new_data,
                    std::vector<std::tuple<u32, u8, T>> &ops, bool &success) {
  
  T new_gap;

  T best_gap = orig_gap;
  u8 best_op = PATA_OP_KEEP;

  success = false;

  for (u32 i = 0; i < PATA_OP_KEEP; ++i) {
    new_data.var_id = 0xFFFFFFFF;
    if (i == PATA_OP_INC) {
      // INC
      buf[offset] += 1;
    } else {
      // DEC
      buf[offset] -= 1;
    }
    if (unlikely(get_specific_pata_data(afl, buf, len, data, new_data))) {
      return 1;
    }
    ++afl->stage_cur;
    if (new_data.var_id != data.var_id) {
      return 0;
    }

    new_gap = calc_gap_for_cmp<T>(new_data);
    if (new_gap < best_gap) {
      best_gap = new_gap;
      best_op = i;
    }
    // recover buf
    if (i == PATA_OP_INC) {
      // INC
      buf[offset] -= 1;
    } else {
      // DEC
      buf[offset] += 1;
    }
  }

  success = true;
  ops.push_back(std::make_tuple(offset, best_op, orig_gap - best_gap));
  return 0;
}

template<typename T> static u8
calc_move_operation_switch(afl_state_t *afl, u8 *buf, u32 len, u32 offset,
                    T orig_gap, T case_value, const PataData &data,
                    PataData &new_data,
                    std::vector<std::tuple<u32, u8, T>> &ops, bool &success) {
  
  T new_gap;

  T best_gap = orig_gap;
  u8 best_op = PATA_OP_KEEP;
  success = false;

  for (u32 i = 0; i < PATA_OP_KEEP; ++i) {
    new_data.var_id = 0xFFFFFFFF;
    if (i == PATA_OP_INC) {
      // INC
      buf[offset] += 1;
    } else {
      // DEC
      buf[offset] -= 1;
    }
    if (unlikely(get_specific_pata_data(afl, buf, len, data, new_data))) {
      return 1;
    }
    ++afl->stage_cur;
    if (new_data.var_id != data.var_id) {
      return 0;
    }

    new_gap = calc_gap_for_switch<T>(new_data, case_value);
    if (new_gap < best_gap) {
      best_gap = new_gap;
      best_op = i;
    }
    // recover buf
    if (i == PATA_OP_INC) {
      // INC
      buf[offset] -= 1;
    } else {
      // DEC
      buf[offset] += 1;
    }
  }

  success = true;
  ops.push_back(std::make_tuple(offset, best_op, orig_gap - best_gap));
  return 0;
}

template<typename T>
struct OpMore {
  bool operator()(const std::tuple<u32, u8, T> &lhs,
                  const std::tuple<u32, u8, T> &rhs) {
    return std::get<2>(lhs) > std::get<2>(rhs);
  }
};

template<typename T> static u8
do_linear_search_cmp(afl_state_t *afl, u8 *buf, u32 len,
                     const ConstraintVariable &cv, const PataData &data,
                     const std::vector<std::pair<u32, u32>> &cbytes,
                     const std::vector<u8> &orig_hit_cnt,
                     u8 &solved, bool &success) {

#ifdef PATA_PROFILE
  static u64 total_time = 0;
  static u64 total_execs = 0;
  u64 entry_time = get_cur_time_us();
#endif

  T gap, new_gap;
  bool orig_eval, new_eval;
  u8 the_op;
  u32 idx;
  PataData new_data;
  std::vector<std::tuple<u32, u8, T>> ops;
  std::vector<u8> after_hit_cnt;

  gap = calc_gap_for_cmp<T>(data);
  orig_eval = eval_constraint_cmp<T>(cv, data);

  for (auto &range : cbytes) {
    for (u32 i = 0; i < range.second; ++i) {
      if (unlikely(calc_move_operation_cmp<T>(afl, buf, len, range.first + i, gap, data, new_data, ops, success))) {
        return 1;
      }
      if (!success) {
        return 0;
      }
    }
  }

  success = false;
  // sort by difference
  std::sort(ops.begin(), ops.end(), OpMore<T>());

  for (auto &op : ops) {
    the_op = std::get<1>(op);
    idx = std::get<0>(op);

    if (the_op == PATA_OP_KEEP) {
      break;
    }

    while (true) {
      // move
      if (the_op) {
        // dec
        buf[idx] -= 1;
      } else {
        // inc
        buf[idx] += 1;
      }

      // execute it
      new_data.var_id = 0xFFFFFFFF;
      if (unlikely(get_specific_pata_data(afl, buf, len, data, new_data))) {
        return 1;
      }
      ++afl->stage_cur;
      if (new_data.var_id != data.var_id) {
        return 0;
      }

      // solved?
      for (u32 i = 0; i < cv.num_bf; ++i) {
        after_hit_cnt.push_back(afl->fsrv.trace_bits[cv.bf[i]]);
      }
      if (after_hit_cnt != orig_hit_cnt) {
        solved = 1;
      }
      after_hit_cnt.clear();

      new_gap = calc_gap_for_cmp<T>(new_data);
      new_eval = eval_constraint_cmp<T>(cv, new_data);

      if (new_eval != orig_eval) {
        // success, yay!
        if (unlikely(common_fuzz_stuff(afl, buf, len))) {
          return 1;
        }
        success = true;
#ifdef PATA_PROFILE
        total_time += (get_cur_time_us() - entry_time);
        ++total_execs;
        if ((total_execs % 100) == 0) {
          printf("do_linear_search_cmp: avg exec time: %lld us\n", total_time / total_execs);
        }
#endif
        return 0;
      }

      if (new_gap >= gap) {
        if (the_op) {
          // recover
          // dec
          buf[idx] += 1;
        } else {
          // inc
          buf[idx] -= 1;
        }
        break;
      }
      gap = new_gap;
    }
  }

  if (unlikely(common_fuzz_stuff(afl, buf, len))) {
    return 1;
  }

#ifdef PATA_PROFILE
  total_time += (get_cur_time_us() - entry_time);
  ++total_execs;
  if ((total_execs % 100) == 0) {
    printf("do_linear_search_cmp: avg exec time: %lld us\n", total_time / total_execs);
  }
#endif

  return 0;
}

template<typename T> static u8
do_linear_search_switch(afl_state_t *afl, u8 *buf, u32 len, T case_value,
                        const ConstraintVariable &cv, const PataData &data,
                        const std::vector<std::pair<u32, u32>> &cbytes,
                        const std::vector<u8> &orig_hit_cnt,
                        u8 &solved, bool &success) {
#ifdef PATA_PROFILE
  static u64 total_time = 0;
  static u64 total_execs = 0;
  u64 entry_time = get_cur_time_us();
#endif
  
  T gap, new_gap;
  bool orig_eval, new_eval;
  u8 the_op;
  u32 idx;
  PataData new_data;
  std::vector<std::tuple<u32, u8, T>> ops;
  std::vector<u8> after_hit_cnt;

  static_assert(std::is_integral<T>());
  gap = calc_gap_for_switch<T>(data, case_value);
  orig_eval = eval_constraint_switch<T>(data, case_value);

  for (auto &range : cbytes) {
    for (u32 i = 0; i < range.second; ++i) {
      if (unlikely(calc_move_operation_switch<T>(afl, buf, len, range.first + i, gap, case_value, data, new_data, ops, success))) {
        return 1;
      }
      if (!success) {
        return 0;
      }
    }
  }

  success = false;
  // sort by difference
  std::sort(ops.begin(), ops.end(), OpMore<T>());

  for (auto &op : ops) {
    the_op = std::get<1>(op);
    idx = std::get<0>(op);

    if (the_op == PATA_OP_KEEP) {
      break;
    }

    while (true) {
      // move
      if (the_op) {
        // dec
        buf[idx] -= 1;
      } else {
        // inc
        buf[idx] += 1;
      }

      // execute it
      new_data.var_id = 0xFFFFFFFF;
      if (unlikely(get_specific_pata_data(afl, buf, len, data, new_data))) {
        return 1;
      }
      ++afl->stage_cur;
      if (new_data.var_id != data.var_id) {
        return 0;
      }

      // solved?
      for (u32 i = 0; i < cv.num_bf; ++i) {
        after_hit_cnt.push_back(afl->fsrv.trace_bits[cv.bf[i]]);
      }
      if (after_hit_cnt != orig_hit_cnt) {
        solved = 1;
      }
      after_hit_cnt.clear();

      new_gap = calc_gap_for_switch<T>(new_data, case_value);
      new_eval = eval_constraint_switch<T>(new_data, case_value);

      if (new_eval != orig_eval) {
        // solved, yay!
        if (unlikely(common_fuzz_stuff(afl, buf, len))) {
          return 1;
        }
#ifdef PATA_PROFILE
        total_time += (get_cur_time_us() - entry_time);
        ++total_execs;
        if ((total_execs % 100) == 0) {
          printf("do_linear_search_switch: avg exec time: %lld us\n", total_time / total_execs);
        }
#endif
        success = true;
        return 0;
      }
      if (new_gap >= gap) {
        if (the_op) {
          // recover
          // dec
          buf[idx] += 1;
        } else {
          // inc
          buf[idx] -= 1;
        }
        break;
      }
      gap = new_gap;
    }
  }
  if (unlikely(common_fuzz_stuff(afl, buf, len))) {
    return 1;
  }

#ifdef PATA_PROFILE
  total_time += (get_cur_time_us() - entry_time);
  ++total_execs;
  if ((total_execs % 100) == 0) {
    printf("do_linear_search_switch: avg exec time: %lld us\n", total_time / total_execs);
  }
#endif

  return 0;
}

// The implementation of linear search is slightly different from the paper. In
// the paper, invalid gaps are considered bigger than others. While in this
// implementation, such testcases are omitted from being mutated by linear
// search because it's faster.

// Also, this linear search seems to be too dependent on the testcase because 
// the weight is not adaptive.
static u8 linear_search(afl_state_t *afl, u8 *orig_buf, u8 *buf, u32 len,
                        const PataData &data,
                        const std::vector<std::pair<u32, u32>> &cbytes,
                        const std::vector<u8> &orig_hit_cnt,
                        u8 &solved, bool &success) {
  const ConstraintVariable &cv = afl->pata_metadata[data.var_id];
  success = false;
  if (cv.kind == PATA_KIND_CALL) {
    return 0;
  }

  u64 orig_entries, new_entries, num_exec;
  u8 ret = 0;

  orig_entries = afl->queued_items + afl->saved_crashes;
  num_exec = afl->stage_cur;
  afl->stage_cur = 0;

  switch (cv.kind) {
    case PATA_KIND_CMP: {
      if (cv.operation <= 15) {
        switch (cv.size) {
          case 4: ret = do_linear_search_cmp<float>(afl, buf, len, cv, data, cbytes, orig_hit_cnt, solved, success); break;
          case 8: ret = do_linear_search_cmp<double>(afl, buf, len, cv, data, cbytes, orig_hit_cnt, solved, success); break;
          default: FATAL("should not happen");
        }
      } else {
        switch (cv.size) {
          case 1: ret = do_linear_search_cmp<u8>(afl, buf, len, cv, data, cbytes, orig_hit_cnt, solved, success); break;
          case 2: ret = do_linear_search_cmp<u16>(afl, buf, len, cv, data, cbytes, orig_hit_cnt, solved, success); break;
          case 4: ret = do_linear_search_cmp<u32>(afl, buf, len, cv, data, cbytes, orig_hit_cnt, solved, success); break;
          case 8: ret = do_linear_search_cmp<u64>(afl, buf, len, cv, data, cbytes, orig_hit_cnt, solved, success); break;
          default: FATAL("should not happen");
        }
      }
      break;
    }
    case PATA_KIND_SWITCH: {
      u32 num_cases = (cv.misc << 8) | cv.operation;
      for (u32 i = 0; i < num_cases; ++i) {
        switch (cv.size) {
          case 1: {
            if (unlikely(do_linear_search_switch<u8>(afl, buf, len, ((u8*)cv.opaque)[i], cv, data, cbytes, orig_hit_cnt, solved, success))) {
              return 1;
            }
            break;
          };
          case 2: {
            if (unlikely(do_linear_search_switch<u16>(afl, buf, len, ((u16*)cv.opaque)[i], cv, data, cbytes, orig_hit_cnt, solved, success))) {
              return 1;
            }
            break;
          };
          case 4: {
            if (unlikely(do_linear_search_switch<u32>(afl, buf, len, ((u32*)cv.opaque)[i], cv, data, cbytes, orig_hit_cnt, solved, success))) {
              return 1;
            }
            break;
          };
          case 8: {
            if (unlikely(do_linear_search_switch<u64>(afl, buf, len, ((u64*)cv.opaque)[i], cv, data, cbytes, orig_hit_cnt, solved, success))) {
              return 1;
            }
            break;
          };
          default: FATAL("should not happen");
        }
        if (i != num_cases - 1) {
          memcpy(buf, orig_buf, len);
        }
      }
      break;
    }
    default: FATAL("should not happen");
  }

  if (unlikely(ret)) { return 1; }

  new_entries = afl->queued_items + afl->saved_crashes;
  afl->stage_finds[STAGE_LINEAR_SEARCH] += new_entries - orig_entries;
  afl->stage_cycles[STAGE_LINEAR_SEARCH] += afl->stage_cur;
  afl->stage_cur = num_exec;

  return 0;
}

static u8 random_explore(afl_state_t *afl, u8 *orig_buf, u8 *buf, u32 len,
                         const PataData &data,
                         const std::vector<std::pair<u32, u32>> &cbytes,
                         const std::vector<u8> &orig_hit_cnt, u8 &solved) {
#define FLIP_BIT(_ar, _b)                   \
  do {                                      \
                                            \
    u8 *_arf = (u8 *)(_ar);                 \
    u32 _bf = (_b);                         \
    _arf[(_bf) >> 3] ^= (128 >> ((_bf)&7)); \
                                            \
  } while (0)

#ifdef PATA_PROFILE
  static u64 total_time = 0;
  static u64 total_execs = 0;
  u64 entry_time = get_cur_time_us();
#endif

  // enumerate all sections
  u32 use_stacking, r, i, temp_len;
  u8 *out_buf;
  const ConstraintVariable &cv = afl->pata_metadata[data.var_id];
  std::vector<u8> after_hit_cnt;
  u64 before_cov;

  u64 orig_entries, new_entries, num_execs;

  orig_entries = afl->queued_items + afl->saved_crashes;
  num_execs = 0;

  for (auto &range : cbytes) {
    use_stacking = 1 << (1 + rand_below(afl, afl->havoc_stack_pow2));
    out_buf = buf + range.first;
    temp_len = range.second;
    for (i = 0; i < use_stacking; ++i) {
      // copied from fuzz_one_original()
      switch ((r = rand_below(afl, 40))) {
        case 0 ... 3: {
          FLIP_BIT(out_buf, rand_below(afl, temp_len << 3));
          break;
        }
        case 4 ... 7: {
          out_buf[rand_below(afl, temp_len)] =
              interesting_8[rand_below(afl, sizeof(interesting_8))];
          break;
        }
        case 8 ... 9: {
          if (temp_len < 2) { break; }
          *(u16 *)(out_buf + rand_below(afl, temp_len - 1)) =
              interesting_16[rand_below(afl, sizeof(interesting_16) >> 1)];
          break;
        }
        case 10 ... 11: {
          if (temp_len < 2) { break; }
          *(u16 *)(out_buf + rand_below(afl, temp_len - 1)) = SWAP16(
              interesting_16[rand_below(afl, sizeof(interesting_16) >> 1)]);
          break;
        }
        case 12 ... 13: {
          if (temp_len < 4) { break; }
          *(u32 *)(out_buf + rand_below(afl, temp_len - 3)) =
              interesting_32[rand_below(afl, sizeof(interesting_32) >> 2)];
          break;
        }
        case 14 ... 15: {
          if (temp_len < 4) { break; }
          *(u32 *)(out_buf + rand_below(afl, temp_len - 3)) = SWAP32(
              interesting_32[rand_below(afl, sizeof(interesting_32) >> 2)]);
          break;
        }
        case 16 ... 19: {
          out_buf[rand_below(afl, temp_len)] -= 1 + rand_below(afl, ARITH_MAX);
          break;
        }
        case 20 ... 23: {
          out_buf[rand_below(afl, temp_len)] += 1 + rand_below(afl, ARITH_MAX);
          break;
        }
        case 24 ... 25: {
          if (temp_len < 2) { break; }
          u32 pos = rand_below(afl, temp_len - 1);
          *(u16 *)(out_buf + pos) -= 1 + rand_below(afl, ARITH_MAX);
          break;
        }
        case 26 ... 27: {
          if (temp_len < 2) { break; }
          u32 pos = rand_below(afl, temp_len - 1);
          u16 num = 1 + rand_below(afl, ARITH_MAX);
          *(u16 *)(out_buf + pos) =
              SWAP16(SWAP16(*(u16 *)(out_buf + pos)) - num);
          break;
        }
        case 28 ... 29: {
          if (temp_len < 2) { break; }
          u32 pos = rand_below(afl, temp_len - 1);
          *(u16 *)(out_buf + pos) += 1 + rand_below(afl, ARITH_MAX);
          break;
        }
        case 30 ... 31: {
          if (temp_len < 2) { break; }
          u32 pos = rand_below(afl, temp_len - 1);
          u16 num = 1 + rand_below(afl, ARITH_MAX);
          *(u16 *)(out_buf + pos) =
              SWAP16(SWAP16(*(u16 *)(out_buf + pos)) + num);
          break;
        }
        case 32 ... 33: {
          if (temp_len < 4) { break; }
          u32 pos = rand_below(afl, temp_len - 3);
          *(u32 *)(out_buf + pos) -= 1 + rand_below(afl, ARITH_MAX);
          break;
        }
        case 34 ... 35: {
          if (temp_len < 4) { break; }
          u32 pos = rand_below(afl, temp_len - 3);
          u32 num = 1 + rand_below(afl, ARITH_MAX);
          *(u32 *)(out_buf + pos) =
              SWAP32(SWAP32(*(u32 *)(out_buf + pos)) - num);
          break;
        }
        case 36 ... 37: {
          if (temp_len < 4) { break; }
          u32 pos = rand_below(afl, temp_len - 3);
          *(u32 *)(out_buf + pos) += 1 + rand_below(afl, ARITH_MAX);
          break;
        }
        case 38 ... 39: {
          if (temp_len < 4) { break; }
          u32 pos = rand_below(afl, temp_len - 3);
          u32 num = 1 + rand_below(afl, ARITH_MAX);
          *(u32 *)(out_buf + pos) =
              SWAP32(SWAP32(*(u32 *)(out_buf + pos)) + num);
          break;
        }
        default: FATAL("should not happen");
      }
    }

    if (unlikely(common_fuzz_patalog_stuff_filter_all(afl, buf, len))) {
      return 1;
    }

    for (i = 0; i < cv.num_bf; ++i) {
      after_hit_cnt.push_back(afl->fsrv.trace_bits[cv.bf[i]]);
    }
    if (after_hit_cnt != orig_hit_cnt) {
      solved = 1;
    }
    after_hit_cnt.clear();

    before_cov = afl->queued_items + afl->saved_crashes;
    if (unlikely(common_fuzz_stuff(afl, buf, len))) {
      return 1;
    }
    
    ++num_execs;
    memcpy(buf, orig_buf, len);
    if (unlikely((afl->queued_items + afl->saved_crashes) > before_cov)) {
      new_entries = afl->queued_items + afl->saved_crashes;
      afl->stage_finds[STAGE_RANDOM_EXPLORE] += new_entries - orig_entries;
      afl->stage_cycles[STAGE_RANDOM_EXPLORE] += num_execs;
#ifdef PATA_PROFILE
      total_time += (get_cur_time_us() - entry_time);
      ++total_execs;
      if ((total_execs % 100) == 0) {
        printf("random_explore: avg exec time: %lld us\n", total_time / total_execs);
      }
#endif
      return 0;
    }
  }

  new_entries = afl->queued_items + afl->saved_crashes;
  afl->stage_finds[STAGE_RANDOM_EXPLORE] += new_entries - orig_entries;
  afl->stage_cycles[STAGE_RANDOM_EXPLORE] += num_execs;

#ifdef PATA_PROFILE
  total_time += (get_cur_time_us() - entry_time);
  ++total_execs;
  if ((total_execs % 100) == 0) {
    printf("random_explore: avg exec time: %lld us\n", total_time / total_execs);
  }
#endif
  return 0;
#undef FLIP_BIT
}

extern "C"
u8 pata_stage(afl_state_t *afl, u8 *orig_buf, u8 *buf, u32 len) {
  const PataSeqPerVar *seq_per_var;
  const PataDataSeq *RVS;
  const CricBytesTy *cric_bytes;
  const UnstableVarTy *unstable_var;
  std::vector<u8> *solved;
  const ConstraintVariable *cv;
  bool success;

  if (likely(afl->queue_cur->exec_us)) {

    if (likely((100000 / 2) >= afl->queue_cur->exec_us)) {

      screen_update = 100000 / afl->queue_cur->exec_us;

    } else {

      screen_update = 1;

    }

  } else {

    screen_update = 100000;

  }

  // Get RVS for this testcase
  if (!afl->queue_cur->RVS) {
    afl->queue_cur->RVS = new PataDataSeq();
    if (unlikely(get_RVS(afl, buf, len, *(PataDataSeq*)afl->queue_cur->RVS))) {
      delete (PataDataSeq*)afl->queue_cur->RVS;
      afl->queue_cur->RVS = nullptr;
      return 1;
    }
  }
  RVS = (PataDataSeq*)afl->queue_cur->RVS;

  // init solved
  if (!afl->queue_cur->solved) {
    afl->queue_cur->solved = new std::vector<u8>();
    solved = (std::vector<u8>*)afl->queue_cur->solved;
    solved->reserve(RVS->size());
    std::fill(solved->begin(), solved->end(), 0);
  }
  solved = (std::vector<u8>*)afl->queue_cur->solved;

  // Store pata map
  if (unlikely(!afl->orig_pata_map)) {
    afl->orig_pata_map = (u8*)ck_alloc(PATALOG_MAP_SIZE);
  }
  memcpy(afl->orig_pata_map, afl->shm.pata_map, ((u32*)afl->shm.pata_map)[1]);

  // Store cov map
  if (unlikely(!afl->orig_map)) {
    afl->orig_map = (u8*)ck_alloc(afl->fsrv.map_size);
  }
  memcpy(afl->orig_map, afl->fsrv.trace_bits, afl->fsrv.map_size);

  // Get sequence for each variable
  if (!afl->queue_cur->seq_per_var) {
    afl->queue_cur->seq_per_var = new PataSeqPerVar();
    get_seq_for_each_var(*RVS, *(PataSeqPerVar*)afl->queue_cur->seq_per_var);
  }
  seq_per_var = (PataSeqPerVar*)afl->queue_cur->seq_per_var;

  // Get unstable variable
  if (!afl->queue_cur->unstable_var) {
    afl->queue_cur->unstable_var = new UnstableVarTy();
    if (unlikely(get_unstable_var(afl, buf, len,
        *(UnstableVarTy*)afl->queue_cur->unstable_var, *seq_per_var))) {
      delete (UnstableVarTy*)afl->queue_cur->unstable_var;
      afl->queue_cur->unstable_var = nullptr;
      return 1;
    }
  }
  unstable_var = (UnstableVarTy*)afl->queue_cur->unstable_var;

  // Get critical bytes for this testcase
  if (!afl->queue_cur->critical_bytes) {
    afl->queue_cur->critical_bytes = new CricBytesTy();
    if (unlikely(collect_critical_bytes(afl, buf, len, *unstable_var,
        *seq_per_var, *(CricBytesTy*)afl->queue_cur->critical_bytes))) {
        delete (CricBytesTy*)afl->queue_cur->critical_bytes;
        afl->queue_cur->critical_bytes = nullptr;
        return 1;
    }
  }
  cric_bytes = (CricBytesTy*)afl->queue_cur->critical_bytes;

  u32 cur_idx = 0xFFFFFFFF;
  std::vector<u8> orig_cov;

  afl->stage_name = (u8*)"PATA";
  afl->stage_short = (u8*)"PATA";
  afl->stage_max = RVS->size();
  afl->stage_cur = 0;

  for (auto &v : *RVS) {
    ++cur_idx;
    if (++afl->stage_cur % screen_update == 0) { show_stats(afl); }
    if (!is_meaningful_to_mutate(v, *unstable_var, (*solved)[cur_idx])) {
      continue;
    }

    orig_cov.clear();
    cv = &afl->pata_metadata[v.var_id];
    for (u32 i = 0; i < cv->num_bf; ++i) {
      orig_cov.push_back(afl->orig_map[cv->bf[i]]);
    }

    if (cv->num_bf < 2) {
      (*solved)[cur_idx] = 1;
    }

    if (unlikely(length_explore(afl, buf, len, v, orig_cov, (*solved)[cur_idx], success))) {
      return 1;
    }
    if (success) {
      continue;
    }

    auto index = std::make_pair(v.var_id, v.occur_id);
    auto cric_it = cric_bytes->find(index);
    if (cric_it == cric_bytes->end()) {
      continue;
    }
    auto &cbytes = cric_it->second;
    if (cbytes.empty()) {
      continue;
    }

    if (unlikely(copy_explore(afl, orig_buf, buf, len, v, cbytes, orig_cov, (*solved)[cur_idx], success))) {
      return 1;
    }
    if (success) {
      continue;
    }

    if (unlikely(linear_search(afl, orig_buf, buf, len, v, cbytes, orig_cov, (*solved)[cur_idx], success))) {
      return 1;
    }
    if (success) {
      memcpy(buf, orig_buf, len);
      continue;
    }

    if (unlikely(random_explore(afl, orig_buf, buf, len, v, cbytes, orig_cov, (*solved)[cur_idx]))) {
      return 1;
    }

    memcpy(buf, orig_buf, len);
  }

  return 0;
}