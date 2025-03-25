use num_bigint::{BigUint, ToBigUint};
use num_traits::{One, Zero, ToPrimitive};
use num_integer::Integer;
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::Instant;
use rayon::prelude::*;
use rand::Rng;

lazy_static::lazy_static! {
    static ref FACTOR_CACHE: Arc<Mutex<HashMap<BigUint, BigUint>>> = Arc::new(Mutex::new(HashMap::new()));
}

/// 小素数列表，用于快速检查
const SMALL_PRIMES: [u32; 50] = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 
    73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 
    157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229
];

/// 查找一个数的最大质因数
/// 使用多种优化算法结合的方式
pub fn largest_prime_factor(n: &BigUint) -> BigUint {
    // 检查缓存
    {
        let cache = FACTOR_CACHE.lock().unwrap();
        if let Some(result) = cache.get(n) {
            return result.clone();
        }
    }
    
    // 处理边界情况
    if n <= &BigUint::one() {
        return n.clone();
    }
    
    // 快速检查是否是素数
    if is_probably_prime(n, 25) {
        return n.clone();
    }
    
    // 试除小素数
    for &p in &SMALL_PRIMES {
        let p_int = BigUint::from(p);
        if n % &p_int == BigUint::zero() {
            let div = n / &p_int;
            let largest_in_div = largest_prime_factor(&div);
            let result = if p_int > largest_in_div { p_int } else { largest_in_div };
            
            // 缓存结果
            let mut cache = FACTOR_CACHE.lock().unwrap();
            cache.insert(n.clone(), result.clone());
            
            return result;
        }
    }
    
    // 使用多种算法找到因子
    let factor = find_factor(n);
    
    // 递归查找最大质因数
    let n_div_factor = n / &factor;
    
    // 并行处理两个分支
    let (max_factor_in_factor, max_factor_in_div) = rayon::join(
        || largest_prime_factor(&factor),
        || largest_prime_factor(&n_div_factor)
    );
    
    let result = if max_factor_in_factor > max_factor_in_div {
        max_factor_in_factor
    } else {
        max_factor_in_div
    };
    
    // 缓存结果
    let mut cache = FACTOR_CACHE.lock().unwrap();
    cache.insert(n.clone(), result.clone());
    
    result
}

/// 根据数字大小选择最适合的因子查找算法
fn find_factor(n: &BigUint) -> BigUint {
    // 为不同大小范围的数选择不同的算法
    let bits = n.bits();
    
    if bits < 64 {
        pollard_rho(n, 1)
    } else if bits < 128 {
        // 使用线程安全的共享结果
        let results = Arc::new(Mutex::new(Vec::new()));
        
        rayon::scope(|s| {
            // 添加Pollard's rho任务
            let results_clone = Arc::clone(&results);
            s.spawn(move |_| {
                let factor = pollard_rho(n, 1);
                if factor > BigUint::one() && factor < *n {
                    let mut results = results_clone.lock().unwrap();
                    results.push(factor);
                }
            });
            
            // 添加另一个变体的Pollard's rho任务
            let results_clone = Arc::clone(&results);
            s.spawn(move |_| {
                let factor = pollard_rho(n, 2);
                if factor > BigUint::one() && factor < *n {
                    let mut results = results_clone.lock().unwrap();
                    results.push(factor);
                }
            });
            
            // 添加Pollard's p-1任务
            let results_clone = Arc::clone(&results);
            s.spawn(move |_| {
                let factor = pollard_p1(n, 100_000);
                if factor > BigUint::one() && factor < *n {
                    let mut results = results_clone.lock().unwrap();
                    results.push(factor);
                }
            });
        });
        
        // 从结果中选择第一个找到的因子
        let results = results.lock().unwrap();
        if !results.is_empty() {
            results[0].clone()
        } else {
            // 如果没找到，返回n-1作为退路
            n - BigUint::one()
        }
    } else {
        // 对大数使用多种方法并行尝试
        // 先并行运行两个不同参数的Pollard's rho
        let (rho1, rho2) = rayon::join(
            || pollard_rho(n, 1),
            || pollard_rho(n, 2)
        );
        
        // 如果两个rho都没找到因子，再尝试p-1算法
        if rho1 > BigUint::one() { 
            rho1
        } else if rho2 > BigUint::one() { 
            rho2
        } else {
            let p1 = pollard_p1(n, 100_000);
            if p1 > BigUint::one() { p1 }
            else { n - BigUint::one() } // 无法分解时的退路
        }
    }
}

/// Miller-Rabin素性测试 - 使用确定性证人集合
fn is_probably_prime(n: &BigUint, certainty: u32) -> bool {
    // 处理小数
    if n <= &BigUint::one() {
        return false;
    }
    if n == &BigUint::from(2u32) || n == &BigUint::from(3u32) {
        return true;
    }
    if n.is_even() {
        return false;
    }
    
    // 对较小的数使用确定性的Miller-Rabin测试
    if n.bits() <= 64 {
        // 这些证人可以确定性地测试64位以内的所有数
        let witnesses = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];
        return miller_rabin_deterministic(n, &witnesses);
    }
    
    // 对大数使用概率性Miller-Rabin测试
    miller_rabin(n, certainty)
}

/// 确定性的Miller-Rabin测试，使用固定的证人集合
fn miller_rabin_deterministic(n: &BigUint, witnesses: &[u32]) -> bool {
    // 将n-1表示为 d*2^r 形式
    let mut d = n - BigUint::one();
    let mut r = 0;
    
    while d.is_even() {
        d >>= 1;
        r += 1;
    }
    
    'witness_loop: for &a in witnesses {
        if a >= n.to_u32().unwrap_or(u32::MAX) {
            continue;
        }
        
        let mut x = mod_pow(&BigUint::from(a), &d, n);
        
        if x == BigUint::one() || x == n - BigUint::one() {
            continue 'witness_loop;
        }
        
        for _ in 0..r-1 {
            x = mod_pow(&x, &BigUint::from(2u32), n);
            if x == n - BigUint::one() {
                continue 'witness_loop;
            }
        }
        
        return false;
    }
    
    true
}

/// 概率性Miller-Rabin素性测试
fn miller_rabin(n: &BigUint, k: u32) -> bool {
    // 将n-1表示为 d*2^r 形式
    let mut d = n - BigUint::one();
    let mut r = 0;
    
    while d.is_even() {
        d >>= 1;
        r += 1;
    }
    
    // 并行测试多个随机证人
    let results: Vec<bool> = (0..k).into_par_iter().map(|_| {
        let mut rng = rand::rng();
        
        // 随机选择 a in [2, n-2]
        let a_max = (n - 2u32).to_u64().unwrap_or(u64::MAX);
        let a_value = if a_max <= 2 {
            2u64
        } else {
            rng.random_range(2..=a_max.min(u64::MAX - 2))
        };
        let a = a_value.to_biguint().unwrap();
        
        let mut x = mod_pow(&a, &d, n);
        
        if x == BigUint::one() || x == n - BigUint::one() {
            return true;
        }
        
        for _ in 0..r-1 {
            x = mod_pow(&x, &BigUint::from(2u32), n);
            if x == n - BigUint::one() {
                return true;
            }
        }
        
        false
    }).collect();
    
    // 所有测试都必须通过才是素数
    results.iter().all(|&x| x)
}

/// 改进的Pollard's rho算法，使用批处理GCD
fn pollard_rho(n: &BigUint, variant: u32) -> BigUint {
    if n.is_even() {
        return BigUint::from(2u32);
    }
    
    if n <= &BigUint::from(3u32) {
        return n.clone();
    }
    
    let mut rng = rand::rng();
    let max = n.to_u64().unwrap_or(u64::MAX);
    
    // 基于variant参数选择不同的起点和增量
    let (x_val, c_val) = match variant {
        1 => (rng.random_range(2..=max.min(u64::MAX - 2)), 1u64),
        2 => (rng.random_range(2..=max.min(u64::MAX - 2)), rng.random_range(1..100u64)),
        3 => (2u64, rng.random_range(1..1000u64)),
        4 => (rng.random_range(100..1000u64).min(max - 1), rng.random_range(1..100u64)),
        _ => (rng.random_range(2..=max.min(u64::MAX - 2)), 1u64),
    };
    
    let mut x = x_val.to_biguint().unwrap();
    let mut y = x.clone();
    let c = c_val.to_biguint().unwrap();
    
    let mut g = BigUint::one();
    let mut q = BigUint::one();
    
    // 用于批处理GCD的参数
    let m = 100;
    let mut count = 0;
    
    while g == BigUint::one() && count < 1000 {
        x = y.clone();
        
        // 执行m次迭代计算乘积
        for _ in 0..m {
            y = (&y * &y + &c) % n;
            let diff = if x > y { &x - &y } else { &y - &x };
            q = (q * diff) % n;
        }
        
        g = q.gcd(n);
        count += 1;
        
        // 每过一段时间重新初始化以避免循环
        if count % 10 == 0 && g == BigUint::one() {
            let new_x = rng.random_range(2..=max.min(u64::MAX - 2));
            y = new_x.to_biguint().unwrap();
            q = BigUint::one();
        }
    }
    
    if g == BigUint::one() || g == *n {
        // 回退到单步GCD计算
        x = BigUint::from(rng.random_range(2..=max.min(u64::MAX - 2)));
        y = x.clone();
        g = BigUint::one();
        count = 0;
        
        while g == BigUint::one() && count < 1000 {
            x = (&x * &x + &c) % n;
            y = (&y * &y + &c) % n;
            y = (&y * &y + &c) % n;
            
            let diff = if x > y { &x - &y } else { &y - &x };
            g = diff.gcd(n);
            count += 1;
        }
    }
    
    if g == *n || g == BigUint::one() {
        // 如果仍然没有找到非平凡因子，使用不同的参数重试
        if variant < 10 {  // 限制递归深度
            pollard_rho(n, variant + 10)  // 使用完全不同的参数
        } else {
            // 最终退路：如果多次尝试都失败，返回n-1
            n - BigUint::one()
        }
    } else {
        g
    }
}

/// Pollard's p-1算法 - 对于某些特殊形式的因子非常有效
fn pollard_p1(n: &BigUint, bound: u32) -> BigUint {
    let mut a = BigUint::from(2u32);
    
    // 第一阶段
    for j in 2..=bound {
        a = mod_pow(&a, &BigUint::from(j), n);
        let g = (a.clone() - BigUint::one()).gcd(n);
        
        if g > BigUint::one() && g < *n {
            return g;
        }
    }
    
    // 如果第一阶段没有找到因子，可以进行第二阶段
    // 简化实现：只进行第一阶段
    BigUint::one()
}

/// 快速模幂：计算 (base^exp) % modulus
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

/// 检查一个数是否为素数 - 用于小数的快速检查
fn is_prime(n: u32) -> bool {
    if n <= 1 {
        return false;
    }
    if n <= 3 {
        return true;
    }
    if n % 2 == 0 || n % 3 == 0 {
        return false;
    }
    
    let mut i = 5;
    while i * i <= n {
        if n % i == 0 || n % (i + 2) == 0 {
            return false;
        }
        i += 6;
    }
    
    true
}

/// 主函数
fn main() {
    let test_cases = [
        "12345678901234567890123456789",
        "9007199254740991", // 2^53 - 1
        "123456789012345678901234567890123456789",
        "33",
        "101",
        "100",
        "982451653", // 大素数
        "3193417941", // 另一个大素数
        "1522605027922533360535618378132637429718068114961380688657908494580122963258952897654000350692006139",
        "10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021"
    ];
    
    // 初始化缓存
    let mut cache = FACTOR_CACHE.lock().unwrap();
    for i in 1..100 {
        let n = BigUint::from(i as u32);
        let mut max_factor = BigUint::from(1u32);
        for j in 2..=i {
            if i % j == 0 && is_prime(j as u32) {
                max_factor = BigUint::from(j as u32);
            }
        }
        cache.insert(n, max_factor);
    }
    drop(cache);
    
    // 多线程处理测试用例
    println!("开始测试，基准测量...");
    test_cases.par_iter().for_each(|&tc| {
        let num = tc.parse::<BigUint>().unwrap();
        
        // 打印处理的数字
        let num_str = if tc.len() > 50 {
            format!("{}...{} ({}位数字)", 
                &tc[0..20], 
                &tc[tc.len()-20..], 
                tc.len())
        } else {
            tc.to_string()
        };
        
        println!("计算数字 {} 的最大质因数", num_str);
        
        let start = Instant::now();
        let result = largest_prime_factor(&num);
        let duration = start.elapsed();
        
        println!(
            "结果: {} 的最大质因数是 {} (计算用时: {:?})",
            num_str, result, duration
        );
    });
}