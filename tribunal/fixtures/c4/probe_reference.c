/* C4 native-ABI probe, Reference direction (corpus family C4, plan §18;
 * bead fln-lld). Compiled by the optional D2 system C compiler as TEST
 * APPARATUS ONLY (§6.6): against the PINNED toolchain's lean.h, linked to
 * the real Reference runtime (libleanshared). Emits layout and behavior
 * facts as NDJSON; the e2e scenario diffs them against the identical facts
 * emitted by Marrow (fln-unsafe-abi c4_probe_emit_facts).
 *
 * Fact keys and operation scripts MUST stay in lockstep with
 * crates/fln-unsafe-abi/src/tests.rs::collect_c4_facts.
 *
 * The lean_object header fields m_cs_sz/m_other/m_tag are C bitfields, so
 * offsetof is illegal on them; their byte positions are derived BEHAVIORALLY
 * (set a sentinel, find its bytes) — which is also the stronger fact.
 */

#include <lean/lean.h>
#include <stdarg.h>
#include <stdio.h>
#include <string.h>
#include <stddef.h>
#include <stdint.h>

static void fact(const char *probe, long long value) {
    printf("{\"schema\":\"fln-c4-abi-probe/1\",\"probe\":\"%s\",\"value\":%lld}\n",
           probe, value);
}

static void factf(long long value, const char *fmt, ...) {
    char buf[256];
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(buf, sizeof buf, fmt, ap);
    va_end(ap);
    fact(buf, value);
}

/* Behavioral byte position of a header bitfield: set a sentinel in an
 * otherwise-zero header, return the index of its low byte. */
static long long header_bitfield_offset(int which) {
    lean_object o;
    memset(&o, 0, sizeof o);
    unsigned char bytes[8];
    switch (which) {
    case 0: o.m_cs_sz = 0xBBAA; break;
    case 1: o.m_other = 0xCC; break;
    default: o.m_tag = 0xDD; break;
    }
    memcpy(bytes, &o, 8);
    for (int i = 0; i < 8; i++) {
        unsigned char probe_byte = which == 0 ? 0xAA : (which == 1 ? 0xCC : 0xDD);
        if (bytes[i] == probe_byte) return i;
    }
    return -1;
}

static lean_object *probe_closure_fn(lean_object *a1, lean_object *a2, lean_object *a3) {
    (void)a2; (void)a3;
    return a1; /* never invoked; the closure is only a layout/RC subject */
}

int main(void) {
    /* ---- layout facts: sizeof + offsetof per contract struct ---- */
    fact("sizeof.lean_object", (long long)sizeof(lean_object));
    fact("offsetof.lean_object.m_rc", (long long)offsetof(lean_object, m_rc));
    fact("offsetof.lean_object.m_cs_sz", header_bitfield_offset(0));
    fact("offsetof.lean_object.m_other", header_bitfield_offset(1));
    fact("offsetof.lean_object.m_tag", header_bitfield_offset(2));

    fact("sizeof.lean_ctor_object", (long long)sizeof(lean_ctor_object));
    fact("offsetof.lean_ctor_object.m_header", (long long)offsetof(lean_ctor_object, m_header));
    fact("offsetof.lean_ctor_object.m_objs", (long long)offsetof(lean_ctor_object, m_objs));

    fact("sizeof.lean_array_object", (long long)sizeof(lean_array_object));
    fact("offsetof.lean_array_object.m_header", (long long)offsetof(lean_array_object, m_header));
    fact("offsetof.lean_array_object.m_size", (long long)offsetof(lean_array_object, m_size));
    fact("offsetof.lean_array_object.m_capacity", (long long)offsetof(lean_array_object, m_capacity));
    fact("offsetof.lean_array_object.m_data", (long long)offsetof(lean_array_object, m_data));

    fact("sizeof.lean_sarray_object", (long long)sizeof(lean_sarray_object));
    fact("offsetof.lean_sarray_object.m_header", (long long)offsetof(lean_sarray_object, m_header));
    fact("offsetof.lean_sarray_object.m_size", (long long)offsetof(lean_sarray_object, m_size));
    fact("offsetof.lean_sarray_object.m_capacity", (long long)offsetof(lean_sarray_object, m_capacity));
    fact("offsetof.lean_sarray_object.m_data", (long long)offsetof(lean_sarray_object, m_data));

    fact("sizeof.lean_string_object", (long long)sizeof(lean_string_object));
    fact("offsetof.lean_string_object.m_header", (long long)offsetof(lean_string_object, m_header));
    fact("offsetof.lean_string_object.m_size", (long long)offsetof(lean_string_object, m_size));
    fact("offsetof.lean_string_object.m_capacity", (long long)offsetof(lean_string_object, m_capacity));
    fact("offsetof.lean_string_object.m_length", (long long)offsetof(lean_string_object, m_length));
    fact("offsetof.lean_string_object.m_data", (long long)offsetof(lean_string_object, m_data));

    fact("sizeof.lean_closure_object", (long long)sizeof(lean_closure_object));
    fact("offsetof.lean_closure_object.m_header", (long long)offsetof(lean_closure_object, m_header));
    fact("offsetof.lean_closure_object.m_fun", (long long)offsetof(lean_closure_object, m_fun));
    fact("offsetof.lean_closure_object.m_arity", (long long)offsetof(lean_closure_object, m_arity));
    fact("offsetof.lean_closure_object.m_num_fixed", (long long)offsetof(lean_closure_object, m_num_fixed));
    fact("offsetof.lean_closure_object.m_objs", (long long)offsetof(lean_closure_object, m_objs));

    fact("sizeof.lean_ref_object", (long long)sizeof(lean_ref_object));
    fact("offsetof.lean_ref_object.m_header", (long long)offsetof(lean_ref_object, m_header));
    fact("offsetof.lean_ref_object.m_value", (long long)offsetof(lean_ref_object, m_value));

    fact("sizeof.lean_thunk_object", (long long)sizeof(lean_thunk_object));
    fact("offsetof.lean_thunk_object.m_header", (long long)offsetof(lean_thunk_object, m_header));
    fact("offsetof.lean_thunk_object.m_value", (long long)offsetof(lean_thunk_object, m_value));
    fact("offsetof.lean_thunk_object.m_closure", (long long)offsetof(lean_thunk_object, m_closure));

    fact("sizeof.lean_task_imp", (long long)sizeof(lean_task_imp));
    fact("offsetof.lean_task_imp.m_closure", (long long)offsetof(lean_task_imp, m_closure));
    fact("offsetof.lean_task_imp.m_head_dep", (long long)offsetof(lean_task_imp, m_head_dep));
    fact("offsetof.lean_task_imp.m_next_dep", (long long)offsetof(lean_task_imp, m_next_dep));
    fact("offsetof.lean_task_imp.m_prio", (long long)offsetof(lean_task_imp, m_prio));
    fact("offsetof.lean_task_imp.m_canceled", (long long)offsetof(lean_task_imp, m_canceled));
    fact("offsetof.lean_task_imp.m_keep_alive", (long long)offsetof(lean_task_imp, m_keep_alive));
    fact("offsetof.lean_task_imp.m_deleted", (long long)offsetof(lean_task_imp, m_deleted));

    fact("sizeof.lean_task_object", (long long)sizeof(lean_task_object));
    fact("offsetof.lean_task_object.m_header", (long long)offsetof(lean_task_object, m_header));
    fact("offsetof.lean_task_object.m_value", (long long)offsetof(lean_task_object, m_value));
    fact("offsetof.lean_task_object.m_imp", (long long)offsetof(lean_task_object, m_imp));

    fact("sizeof.lean_promise_object", (long long)sizeof(lean_promise_object));
    fact("offsetof.lean_promise_object.m_header", (long long)offsetof(lean_promise_object, m_header));
    fact("offsetof.lean_promise_object.m_result", (long long)offsetof(lean_promise_object, m_result));

    fact("sizeof.lean_external_class", (long long)sizeof(lean_external_class));
    fact("offsetof.lean_external_class.m_finalize", (long long)offsetof(lean_external_class, m_finalize));
    fact("offsetof.lean_external_class.m_foreach", (long long)offsetof(lean_external_class, m_foreach));

    fact("sizeof.lean_external_object", (long long)sizeof(lean_external_object));
    fact("offsetof.lean_external_object.m_header", (long long)offsetof(lean_external_object, m_header));
    fact("offsetof.lean_external_object.m_class", (long long)offsetof(lean_external_object, m_class));
    fact("offsetof.lean_external_object.m_data", (long long)offsetof(lean_external_object, m_data));

    /* ---- tagged scalars ---- */
    {
        size_t ns[4] = {0, 1, 41, (size_t)1 << 20};
        for (int i = 0; i < 4; i++) {
            factf((long long)(uintptr_t)lean_box(ns[i]), "box.%zu.bits", ns[i]);
            factf((long long)lean_obj_tag(lean_box(ns[i])), "box.%zu.tag", ns[i]);
        }
    }

    /* ---- ctor: header facts + scalar packing (2 slots, 8 scalar bytes) ---- */
    {
        lean_object *o = lean_alloc_ctor(7, 2, 8);
        lean_ctor_set(o, 0, lean_box(1));
        lean_ctor_set(o, 1, lean_box(2));
        lean_ctor_set_uint8(o, 16, 0xAB);
        lean_ctor_set_uint8(o, 17, 0xCD);
        for (unsigned i = 18; i < 24; i++) lean_ctor_set_uint8(o, i, 0);
        fact("ctor.7_2_8.rc", (long long)o->m_rc);
        fact("ctor.7_2_8.cs_sz", (long long)o->m_cs_sz);
        fact("ctor.7_2_8.other", (long long)o->m_other);
        fact("ctor.7_2_8.tag", (long long)o->m_tag);
        fact("ctor.7_2_8.scalar_u64", (long long)lean_ctor_get_uint64(o, 16));
        lean_dec(o);
    }

    /* ---- padded-word zero law (1 slot + 1 scalar byte) ---- */
    {
        lean_object *o = lean_alloc_ctor(0, 1, 1);
        lean_ctor_set(o, 0, lean_box(3));
        lean_ctor_set_uint8(o, 8, 0x7F);
        fact("ctor.padzero.scalar_u64", (long long)lean_ctor_get_uint64(o, 8));
        lean_dec(o);
    }

    /* ---- string semantics ---- */
    {
        lean_object *s = lean_mk_string("h\xc3\xa9llo\xe2\x88\x80");
        fact("string.hello.size", (long long)lean_string_size(s));
        fact("string.hello.capacity", (long long)lean_string_capacity(s));
        fact("string.hello.length", (long long)lean_string_len(s));
        fact("string.hello.cs_sz", (long long)s->m_cs_sz);
        fact("string.hello.byte0", (long long)(unsigned char)lean_string_cstr(s)[0]);
        fact("string.hello.nul",
             (long long)(unsigned char)lean_string_cstr(s)[lean_string_size(s) - 1]);
        lean_dec(s);
        lean_object *e = lean_mk_string("");
        fact("string.empty.size", (long long)lean_string_size(e));
        fact("string.empty.length", (long long)lean_string_len(e));
        lean_dec(e);
    }

    /* ---- array / sarray ---- */
    {
        lean_object *a = lean_alloc_array(3, 3);
        lean_array_cptr(a)[0] = lean_box(1);
        lean_array_cptr(a)[1] = lean_box(2);
        lean_array_cptr(a)[2] = lean_box(3);
        fact("array.3.size", (long long)lean_array_size(a));
        fact("array.3.capacity", (long long)lean_array_capacity(a));
        fact("array.3.cs_sz", (long long)a->m_cs_sz);
        lean_dec(a);
        lean_object *sa = lean_alloc_sarray(4, 2, 2);
        memset(lean_sarray_cptr(sa), 0, 8);
        lean_sarray_cptr(sa)[0] = 9;
        lean_sarray_cptr(sa)[4] = 8;
        fact("sarray.4_2.elem_size", (long long)lean_sarray_elem_size(sa));
        fact("sarray.4_2.cs_sz", (long long)sa->m_cs_sz);
        lean_dec(sa);
    }

    /* ---- closure ---- */
    {
        lean_object *cl = lean_alloc_closure((void *)probe_closure_fn, 3, 1);
        lean_closure_set(cl, 0, lean_box(1));
        fact("closure.3_1.arity", (long long)lean_closure_arity(cl));
        fact("closure.3_1.num_fixed", (long long)lean_closure_num_fixed(cl));
        fact("closure.3_1.cs_sz", (long long)cl->m_cs_sz);
        lean_dec(cl);
    }

    /* ---- tri-state RC transitions ---- */
    {
        lean_object *r = lean_mk_string("rc-probe");
        lean_inc(r);
        lean_inc(r);
        fact("rc.st.after_2inc", (long long)r->m_rc);
        lean_dec(r);
        fact("rc.st.after_dec", (long long)r->m_rc);
        lean_dec(r);
        lean_dec(r);

        lean_object *p = lean_mk_string("persist-probe");
        lean_mark_persistent(p);
        fact("rc.persistent.value", (long long)p->m_rc);
        lean_inc(p);
        lean_dec(p);
        fact("rc.persistent.after_incdec", (long long)p->m_rc);
        /* persistent objects are immortal; deliberately not freed */

        lean_object *m = lean_mk_string("mt-probe");
        lean_mark_mt(m);
        fact("rc.mt.after_mark", (long long)-(m->m_rc));
        lean_inc(m);
        fact("rc.mt.after_inc", (long long)-(m->m_rc));
        lean_dec(m);
        fact("rc.mt.after_dec", (long long)-(m->m_rc));
        lean_dec(m);
    }

    return 0;
}
