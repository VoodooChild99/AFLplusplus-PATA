#include <limits.h>
#include <sys/select.h>

#include "afl-fuzz.h"
#include "patalog.h"

void patalog_exec_child(struct afl_forkserver *fsrv, char **argv) {
  if (fsrv->qemu_mode || fsrv->frida_mode || fsrv->cs_mode) {

    setenv("AFL_DISABLE_LLVM_INSTRUMENTATION", "1", 0);

  }

  if (!fsrv->qemu_mode && !fsrv->frida_mode && argv[0] != fsrv->patalog_binary) {

    fsrv->target_path = argv[0] = fsrv->patalog_binary;

  }

  execv(fsrv->target_path, argv);
}

u8 common_fuzz_patalog_stuff(afl_state_t *afl, u8 *out_buf, u32 len) {
  u8  fault;
  u32 tmp_len = write_to_testcase(afl, (void **)&out_buf, len, 0);
  *((u32*)afl->shm.pata_map) = 0;
  ((u32*)afl->shm.pata_map)[1] = PATA_MAP_HEADER;

  if (likely(tmp_len)) {

    len = tmp_len;

  } else {

    len = write_to_testcase(afl, (void **)&out_buf, len, 1);

  }

  fault = fuzz_run_target(afl, &afl->patalog_fsrv, afl->fsrv.exec_tmout);

  if (afl->stop_soon) { return 1; }

  if (fault == FSRV_RUN_TMOUT) {

    if (afl->subseq_tmouts++ > TMOUT_LIMIT) {

      ++afl->cur_skipped_items;
      return 1;

    }

  } else {

    afl->subseq_tmouts = 0;

  }

  /* Users can hit us with SIGUSR1 to request the current input
     to be abandoned. */

  if (afl->skip_requested) {

    afl->skip_requested = 0;
    ++afl->cur_skipped_items;
    return 1;

  }

  return 0;
}

void add_pata_metadata(afl_state_t *afl, u8 *cv, u32 id) {
  assert(id < afl->num_pata_metadata_entries);
  memcpy(afl->pata_metadata + id, cv, sizeof(ConstraintVariable));
}

void reserve_metadata(afl_state_t *afl, u32 num) {
  if (afl->pata_metadata) {
    return;
  }

  afl->pata_metadata = ck_alloc(num * sizeof(ConstraintVariable));
  afl->num_pata_metadata_entries = num;
}
