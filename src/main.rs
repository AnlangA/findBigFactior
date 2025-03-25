use num_bigint::{BigUint, ToBigUint};
use num_traits::{One, Zero, ToPrimitive};
use num_integer::Integer;
use rand::Rng;
use std::time::Instant;

/// Finds the largest prime factor of a number using probabilistic methods
/// Uses Miller-Rabin primality test and Pollard's rho algorithm for factorization
pub fn largest_prime_factor(n: &BigUint) -> BigUint {
    // Handle edge cases
    if n <= &BigUint::one() {
        return n.clone();
    }
    
    // Check if n is prime using Miller-Rabin
    if is_probably_prime(n, 20) {
        return n.clone();
    }
    
    // Find a factor using Pollard's rho algorithm
    let factor = pollard_rho(n);
    
    // Recursively find the largest prime factor in both the factor and n/factor
    let n_div_factor = n / &factor;
    let max_factor_in_factor = largest_prime_factor(&factor);
    let max_factor_in_div = largest_prime_factor(&n_div_factor);
    
    // Return the larger of the two largest prime factors
    if max_factor_in_factor > max_factor_in_div {
        max_factor_in_factor
    } else {
        max_factor_in_div
    }
}

/// Miller-Rabin primality test
/// Returns true if n is probably prime with high confidence
fn is_probably_prime(n: &BigUint, k: u32) -> bool {
    if n == &BigUint::from(2u32) || n == &BigUint::from(3u32) {
        return true;
    }
    
    if n <= &BigUint::one() || n.is_even() {
        return false;
    }
    
    // Write n-1 as 2^r * d where d is odd
    let mut d = n - BigUint::one();
    let mut r = 0;
    
    while d.is_even() {
        d /= 2u32;
        r += 1;
    }
    
    // Witness loop
    let mut rng = rand::rng();
    'witness: for _ in 0..k {
        // Choose a random integer a in the range [2, n-2]
        let n_minus_two = n - 2u32;
        let max_val = n_minus_two.to_u64().unwrap_or(u64::MAX);
        
        // Use random_range instead of choose to get a random number
        let a_val = if max_val <= 2 {
            2 // Fallback value
        } else {
            rng.random_range(2..=max_val.min(u64::MAX - 2))
        };
        let a = a_val.to_biguint().unwrap();
        
        // x = a^d mod n
        let mut x = mod_pow(&a, &d, n);
        
        if x == BigUint::one() || x == (n - BigUint::one()) {
            continue 'witness;
        }
        
        let mut is_composite = true;
        for _ in 0..r-1 {
            // x = x^2 mod n
            x = mod_pow(&x, &BigUint::from(2u32), n);
            
            if x == (n - BigUint::one()) {
                is_composite = false;
                break;
            }
        }
        
        if is_composite {
            return false;
        }
    }
    
    true
}

/// Pollard's rho algorithm for integer factorization
fn pollard_rho(n: &BigUint) -> BigUint {
    if n.is_even() {
        return BigUint::from(2u32);
    }
    
    let mut rng = rand::rng();
    let max_val = n.to_u64().unwrap_or(u64::MAX) - 1;
    
    // Random value between 1 and max_val
    let x_val = if max_val <= 1 {
        2 // Fallback for very small numbers
    } else {
        rng.random_range(1..=max_val)
    };
    let mut x = x_val.to_biguint().unwrap();
    let mut y = x.clone();
    
    // Random value between 1 and max_val
    let c_val = if max_val <= 1 {
        1 // Fallback for very small numbers
    } else {
        rng.random_range(1..=max_val)
    };
    let mut c = c_val.to_biguint().unwrap();
    
    let mut d = BigUint::one();
    let mut attempts = 0;
    
    while d == BigUint::one() && attempts < 1000 {
        attempts += 1;
        
        // f(x) = x^2 + c mod n
        x = ((&x * &x) + &c) % n;
        
        // y = f(f(y))
        y = ((&y * &y) + &c) % n;
        y = ((&y * &y) + &c) % n;
        
        // Calculate GCD
        let diff = if x > y { &x - &y } else { &y - &x };
        d = gcd(&diff, n);
        
        if &d > &BigUint::one() && d < *n {
            return d;
        }
        
        // Cycle detection - if we've been running too long, try a new random starting point
        if d == *n || attempts >= 100 {
            let new_x_val = if max_val <= 1 {
                2
            } else {
                rng.random_range(1..=max_val)
            };
            x = new_x_val.to_biguint().unwrap();
            y = x.clone();
            
            let new_c_val = if max_val <= 1 {
                1
            } else {
                rng.random_range(1..=max_val)
            };
            c = new_c_val.to_biguint().unwrap();
            
            d = BigUint::one();
            attempts = 0;
        }
    }
    
    // Fallback if we can't factorize
    if d == BigUint::one() {
        return n - BigUint::one();
    }
    
    d
}

/// Modular exponentiation: Computes (base^exp) % modulus efficiently
fn mod_pow(base: &BigUint, exp: &BigUint, modulus: &BigUint) -> BigUint {
    let mut result = BigUint::one();
    let mut base = base.clone() % modulus;
    let mut exp = exp.clone();
    
    while exp > BigUint::zero() {
        if &exp % 2u32 == BigUint::one() {
            result = (result * &base) % modulus;
        }
        exp >>= 1;
        base = (&base * &base) % modulus;
    }
    
    result
}

/// Euclidean algorithm for GCD
fn gcd(a: &BigUint, b: &BigUint) -> BigUint {
    if *b == BigUint::zero() {
        return a.clone();
    }
    gcd(b, &(a % b))
}

/// Example usage
fn main() {
    let test_cases = [
        "12345678901234567890123456789",
        "9007199254740991", // 2^53 - 1
        "123456789012345678901234567890123456789",
        "33",
        "101",
        "100"
    ];
    
    for &tc in &test_cases {
        let num = tc.parse::<BigUint>().unwrap();
        let start = Instant::now();
        let result = largest_prime_factor(&num);
        let duration = start.elapsed();
        println!(
            "Largest prime factor of {} is {} (computed in {:?})",
            tc, result, duration
        );
    }
}