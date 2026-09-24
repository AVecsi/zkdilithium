use winterfell::Proof;
use winterfell::math::{fields::f23201::BaseElement, FieldElement};
use std::io::Write;

pub mod multishowpf;
pub mod disclosurepf2;
pub mod utils;
pub mod test_key;

use crate::disclosurepf2::{Credential, DisclosureInputs};
use crate::utils::poseidon_23_spec::{
    DIGEST_SIZE as HASH_DIGEST_WIDTH,
    RATE_WIDTH as HASH_RATE_WIDTH
};

use crate::multishowpf::{N, K, IssuerKey};
use crate::utils::poseidon_23_spec::STATE_WIDTH as HASH_STATE_WIDTH;

use std::ffi::CStr;
use std::ptr;
use std::slice;
use std::time::{Duration, Instant};

/// Reads an issuer public key out of the three flat C buffers the caller
/// provides: `htr` (HASH_STATE_WIDTH elements), `t` (K*N, `[j][n]`) and `a`
/// (K*K*N, `[i][j][n]`).
///
/// # Safety
/// The three pointers must each be non-null and point to at least the number
/// of `u32`s listed above.
unsafe fn read_issuer_key(htr_ptr: *const u32, t_ptr: *const u32, a_ptr: *const u32) -> IssuerKey {
    let mut htr = [BaseElement::ZERO; HASH_STATE_WIDTH];
    for i in 0..HASH_STATE_WIDTH {
        htr[i] = BaseElement::new(*(htr_ptr.add(i)));
    }

    let mut t = [[BaseElement::ZERO; N]; K];
    for j in 0..K {
        for n in 0..N {
            t[j][n] = BaseElement::new(*(t_ptr.add(j * N + n)));
        }
    }

    let mut a = [[[BaseElement::ZERO; N]; K]; K];
    for i in 0..K {
        for j in 0..K {
            for n in 0..N {
                a[i][j][n] = BaseElement::new(*(a_ptr.add((i * K + j) * N + n)));
            }
        }
    }

    IssuerKey { htr, t, a }
}

#[no_mangle]
pub extern "C" fn prove_signature(z_ptr: *const u32, w_ptr: *const u32, qw_ptr: *const u32, ctilde_ptr: *const u32, m_ptr: *const u32, comm_ptr: *const u32, comr_ptr: *const u32, salt_ptr: *const u32, nonce_ptr: *const u32, htr_ptr: *const u32, t_ptr: *const u32, a_ptr: *const u32, out_proof_bytes_len: *mut usize) -> *const u8 {

    //For now lets just assume that the input's length is ok
    //Convert from the C bytes to something rust readable
    let mut z: [[BaseElement; N]; K] = [[BaseElement::ZERO; N]; K];
    let mut w: [[BaseElement; N]; K] = [[BaseElement::ZERO; N]; K];
    let mut qw: [[BaseElement; N]; K] = [[BaseElement::ZERO; N]; K];
    let mut ctilde: [BaseElement; HASH_DIGEST_WIDTH] = [BaseElement::ZERO; HASH_DIGEST_WIDTH];
    let mut m: [BaseElement; HASH_DIGEST_WIDTH] = [BaseElement::ZERO; HASH_DIGEST_WIDTH];
    let mut comm: [BaseElement; HASH_DIGEST_WIDTH] = [BaseElement::ZERO; HASH_DIGEST_WIDTH];
    let mut com_r: [BaseElement; HASH_DIGEST_WIDTH] = [BaseElement::ZERO; HASH_DIGEST_WIDTH];
    let mut salt: [BaseElement; HASH_DIGEST_WIDTH] = [BaseElement::ZERO; HASH_DIGEST_WIDTH];
    let mut nonce: [BaseElement; HASH_DIGEST_WIDTH] = [BaseElement::ZERO; HASH_DIGEST_WIDTH];

    unsafe {
        for i in 0..K {
            for j in 0..N {
                z[i][j] = BaseElement::new(*(z_ptr.add(i*N+j)));
                w[i][j] = BaseElement::new(*(w_ptr.add(i*N+j)));
                qw[i][j] = BaseElement::new(*(qw_ptr.add(i*N+j)));
            }
        }



        for i in 0..HASH_DIGEST_WIDTH {
            ctilde[i] = BaseElement::new(*(ctilde_ptr.add(i)));
        }

        for i in 0..HASH_DIGEST_WIDTH {
            m[i] = BaseElement::new(*(m_ptr.add(i)));
        }

        for i in 0..HASH_DIGEST_WIDTH {
            comm[i] = BaseElement::new(*(comm_ptr.add(i)));
        }

        for i in 0..HASH_DIGEST_WIDTH {
            com_r[i] = BaseElement::new(*(comr_ptr.add(i)));
        }

        for i in 0..HASH_DIGEST_WIDTH {
            salt[i] = BaseElement::new(*(salt_ptr.add(i)));
        }

        for i in 0..HASH_DIGEST_WIDTH {
            nonce[i] = BaseElement::new(*(nonce_ptr.add(i)));
        }
    }

    let issuer = unsafe { read_issuer_key(htr_ptr, t_ptr, a_ptr) };

    let start = Instant::now();
    let proof_bytes = multishowpf::prove(z, w, qw, ctilde, m, comm, com_r, salt, nonce, issuer).to_bytes();
    println!("{:?}", start.elapsed());

    unsafe {
        *out_proof_bytes_len = proof_bytes.len();
    }

    Vec::leak(proof_bytes).as_ptr()
}

#[no_mangle]
pub extern "C" fn verify_signature(proof_bytes_ptr: *const u8, proof_bytes_len: usize, comm_ptr: *const u32, nonce_ptr: *const u32, htr_ptr: *const u32, t_ptr: *const u32, a_ptr: *const u32) -> u32 {

    let proof = Proof::from_bytes(unsafe {slice::from_raw_parts(proof_bytes_ptr, proof_bytes_len)}).unwrap();
    let mut comm: [BaseElement; HASH_DIGEST_WIDTH] = [BaseElement::ZERO; HASH_DIGEST_WIDTH];
    let mut nonce: [BaseElement; HASH_DIGEST_WIDTH] = [BaseElement::ZERO; HASH_DIGEST_WIDTH];
    unsafe {
        for i in 0..HASH_DIGEST_WIDTH {
            comm[i] = BaseElement::new(*(comm_ptr.add(i)));
        }

        for i in 0..HASH_DIGEST_WIDTH {
            nonce[i] = BaseElement::new(*(nonce_ptr.add(i)));
        }
    }

    let issuer = unsafe { read_issuer_key(htr_ptr, t_ptr, a_ptr) };

    match multishowpf::verify(proof.clone(), comm, nonce, issuer) {
        Ok(_) => {
            //println!("Verified.");
            return 1;
        },
        Err(msg) => 
        {
            println!("Failed to verify proof: {}", msg);
            return 0;
        }
    }
}


#[repr(C)]
pub struct CCredential {
    pub attributes:          *const u32,  // flat: num_attributes * HASH_DIGEST_WIDTH
    pub num_attributes:      usize,
    pub num_user_attributes: usize,
    pub disclosed_indices:   *const usize,
    pub num_disclosed:       usize,
    pub salted_hash:         *const u32,  // HASH_DIGEST_WIDTH elements
    pub salt:                *const u32,  // 12 elements
}

#[repr(C)]
pub struct CDisclosure {
    pub disclosed_attributes: *const u32,  // flat: num_disclosed * HASH_DIGEST_WIDTH
    pub num_disclosed:        usize,
    pub disclosed_indices:    *const usize,
    pub num_all_attributes:   usize,
    pub num_user_attributes:  usize,
    pub salted_hash:          *const u32,  // HASH_DIGEST_WIDTH elements
}

//TODO Should reimplement without flattening
#[no_mangle]
pub extern "C" fn prove_attributes(
    creds: *const CCredential,
    num_creds: usize,
    nonce_ptr: *const u32,
    out_len: *mut usize,
) -> *const u8 {
    let creds = unsafe { std::slice::from_raw_parts(creds, num_creds) };
    let nonce: [BaseElement; HASH_DIGEST_WIDTH] =
        std::array::from_fn(|i| BaseElement::new(unsafe { *nonce_ptr.add(i) }));

    let credentials = creds.iter().map(|c| {
        let attrs_raw = unsafe { slice::from_raw_parts(c.attributes, c.num_attributes * HASH_DIGEST_WIDTH) };
        let attributes = (0..c.num_attributes)
            .map(|j| std::array::from_fn(|k| BaseElement::new(attrs_raw[j * HASH_DIGEST_WIDTH + k])))
            .collect();

        let disclosed_indices = unsafe { slice::from_raw_parts(c.disclosed_indices, c.num_disclosed) }.to_vec();

        let salted_hash = std::array::from_fn(|j| BaseElement::new(unsafe { *c.salted_hash.add(j) }));
        let salt        = std::array::from_fn(|j| BaseElement::new(unsafe { *c.salt.add(j) }));

        Credential{ attributes, num_of_user_attributes: c.num_user_attributes, disclosed_indices, salted_hash, salt }
        }).collect();

    let start = Instant::now();
    let proof_bytes = disclosurepf2::prove(credentials, nonce).to_bytes();
    println!("{:?}", start.elapsed());
    
    unsafe { *out_len = proof_bytes.len(); }
    Vec::leak(proof_bytes).as_ptr()
}

#[no_mangle]
pub extern "C" fn verify_attributes(
    proof_bytes_ptr: *const u8,
    proof_bytes_len: usize,
    discls_ptr: *const CDisclosure,
    num_discls: usize,
    nonce_ptr: *const u32,
) -> u32 {

    let proof = Proof::from_bytes(unsafe {
        slice::from_raw_parts(proof_bytes_ptr, proof_bytes_len)
    }).unwrap();

    let discls = unsafe { slice::from_raw_parts(discls_ptr, num_discls) };

    let disclosures = discls.iter().map(|d| {
        let attrs_raw = unsafe { slice::from_raw_parts(d.disclosed_attributes, d.num_disclosed * HASH_DIGEST_WIDTH) };
        let disclosed_attributes = (0..d.num_disclosed)
            .map(|j| std::array::from_fn(|k| BaseElement::new(attrs_raw[j * HASH_DIGEST_WIDTH + k])))
            .collect();

        let indices = unsafe { slice::from_raw_parts(d.disclosed_indices, d.num_disclosed) }.to_vec();
        let salted_hash = std::array::from_fn(|j| BaseElement::new(unsafe { *d.salted_hash.add(j) }));

        DisclosureInputs {
            disclosed_attributes,
            indices,
            num_of_attributes: d.num_all_attributes,
            num_of_user_attributes: d.num_user_attributes,
            salted_hash,
        }
    }).collect();

    let nonce: [BaseElement; HASH_DIGEST_WIDTH] =
        std::array::from_fn(|i| BaseElement::new(unsafe { *nonce_ptr.add(i) }));

    match disclosurepf2::verify(proof, disclosures, nonce) {
        Ok(_) => 1,
        Err(msg) => {
            println!("Failed to verify proof: {}", msg);
            0
        }
    }
}

#[no_mangle]
pub unsafe extern "C" fn free_proof(ptr: *mut u8, len: usize) {
    drop(Vec::from_raw_parts(ptr, len, len));
}