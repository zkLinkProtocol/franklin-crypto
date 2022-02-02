
use franklin_crypto::plonk::circuit::boolean::Boolean;
pub(crate) use franklin_crypto::bellman::plonk::better_better_cs::cs::*;
use franklin_crypto::bellman::SynthesisError;
use franklin_crypto::bellman::pairing::Engine;
use std::ops::Deref;
use std::collections::HashMap;
use std::sync::Mutex;

lazy_static!{
    static ref GLOBAL_STORAGE: Mutex<Storage> = Mutex::new(Storage::new());
}

//The BooleanWrapper structure is a wrapper to the Boulevard structure. 
//Its main idea is not to allow duplicates of constraints when calling Boolean methods.
#[derive(Debug)]
pub struct BooleanWrapper(Boolean);


impl Deref for BooleanWrapper {
    type Target = Boolean;
    fn deref(&self) -> &Boolean {
        &self.0 
    }
}
impl BooleanWrapper{
    //Inside the structure, Boolean itself is called
    //Also call the methods of the local Storage, which checks whether there is already such 
    // a key with the desired constraint in the database.
    pub fn xor<E, CS>(cs: &mut CS, a: &Boolean, b: &Boolean)-> Result<Self, SynthesisError>
    where E: Engine,
        CS: ConstraintSystem<E>{
            match (a,b){
                (&Boolean::Constant(true), a)|(a, &Boolean::Constant(true))|(&Boolean::Constant(false), a)|(a, &Boolean::Constant(false))=>{
                    Ok(BooleanWrapper(Boolean::xor(cs, &a, &b).unwrap()))
                }
                (_,_)=>{
                    if GLOBAL_STORAGE.lock().unwrap().check_storage(&(a.clone(), b.clone(), String::from("xor"))){
                        return Ok(BooleanWrapper(GLOBAL_STORAGE.lock().unwrap().return_value(&(a.clone(), b.clone(), String::from("xor")))))
                    }
            
                    else{
                        let value = Boolean::xor(cs, &a, &b).unwrap();
                        GLOBAL_STORAGE.lock().unwrap().insert_value((a.clone(), b.clone(), String::from("xor")), &value);
                        Ok(BooleanWrapper(value))
                
                    }
                }
        } 
    }

    pub fn and<E, CS>(cs: &mut CS, a: &Boolean, b: &Boolean)-> Result<Self, SynthesisError>
    where E: Engine,
        CS: ConstraintSystem<E>{
            match (a,b){
                (&Boolean::Constant(true), a)|(a, &Boolean::Constant(true))|(&Boolean::Constant(false), a)|(a, &Boolean::Constant(false))=>{
                    Ok(BooleanWrapper(Boolean::and(cs, &a, &b).unwrap()))
                }

                (_,_)=>{
                    if GLOBAL_STORAGE.lock().unwrap().check_storage(&(a.clone(), b.clone(), String::from("and"))){
                        return Ok(BooleanWrapper(GLOBAL_STORAGE.lock().unwrap().return_value(&(a.clone(), b.clone(), String::from("and")))))
                    }
            
                    else{
                        let value = Boolean::and(cs, &a, &b).unwrap();
                        GLOBAL_STORAGE.lock().unwrap().insert_value((a.clone(), b.clone(), String::from("and")), &value);
                        Ok(BooleanWrapper(value))
                
                    }
                }
        }
    }

    pub fn or<E, CS>(cs: &mut CS, a: &Boolean, b: &Boolean)-> Result<Self, SynthesisError>
    where E: Engine,
        CS: ConstraintSystem<E>{
            match (a,b){
                (&Boolean::Constant(true), a)|(a, &Boolean::Constant(true))|(&Boolean::Constant(false), a)|(a, &Boolean::Constant(false))=>{
                    Ok(BooleanWrapper(Boolean::or(cs, &a, &b).unwrap()))
                }

                (_,_)=>{
                    if GLOBAL_STORAGE.lock().unwrap().check_storage(&(a.clone(), b.clone(), String::from("or"))){
                        return Ok(BooleanWrapper(GLOBAL_STORAGE.lock().unwrap().return_value(&(a.clone(), b.clone(), String::from("or")))))
                    }
            
                    else{
                        let value = Boolean::or(cs, &a, &b).unwrap();
                        GLOBAL_STORAGE.lock().unwrap().insert_value((a.clone(), b.clone(), String::from("or")), &value);
                        Ok(BooleanWrapper(value))
                
                    }
                }
        }
    }

    pub fn conditionally_select<E: Engine, CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        a: &Boolean,
        b: &Boolean
    ) -> Result<Self, SynthesisError> {
        match (a,b){
            (&Boolean::Constant(true), a)|(a, &Boolean::Constant(true))|(&Boolean::Constant(false), a)|(a, &Boolean::Constant(false))=>{
                Ok(BooleanWrapper(Boolean::sha256_ch(cs, &flag, &a, &b).unwrap()))
            }

            (_,_)=>{
                if GLOBAL_STORAGE.lock().unwrap().check_storage(&(a.clone(), b.clone(), String::from("conditionally_select"))){
                    return Ok(BooleanWrapper(GLOBAL_STORAGE.lock().unwrap().return_value(&(a.clone(), b.clone(), String::from("conditionally_select")))))
                }
                
                else{
                    let value = Boolean::sha256_ch(cs, &flag, &a, &b).unwrap();
                    GLOBAL_STORAGE.lock().unwrap().insert_value((a.clone(), b.clone(), String::from("conditionally_select")), &value);
                    Ok(BooleanWrapper(value))
                    
                }
            }
        }
    }

    pub fn alloc<E: Engine, CS: ConstraintSystem<E>>(cs: &mut CS, witness: Option<bool>) -> Result<Self, SynthesisError> {
            Ok(BooleanWrapper(Boolean::alloc(cs, witness).unwrap()))
    }
    
    pub fn convert(&self)-> Boolean{
        self.0

    }

}
use derivative;
pub(crate) use derivative::*;
#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct Storage{
    pub inner: std::collections::HashMap<(Boolean, Boolean, String), Boolean>
}

impl Storage{
    pub fn new() -> Self {
        Self {
            inner: HashMap::new()
        }
    }

    pub fn insert_value(&mut self, key: (Boolean, Boolean, String), value: &Boolean ){
        self.inner.insert(key.clone(), value.clone());
    }

    pub fn check_storage(&self, key: &(Boolean, Boolean, String))->bool{
        return self.inner.contains_key(key);

    }
    pub fn return_value(&self, key: &(Boolean, Boolean, String))->Boolean{
        return *self.inner.get(&key).unwrap();
    }

    pub fn clear_storage(&mut self){
        self.inner.clear();
    }
}

#[cfg(test)]
mod test{

    use franklin_crypto::bellman::pairing::{bn256::Bn256};
    use franklin_crypto::plonk::circuit::boolean::AllocatedBit;
    use super::*;
    #[test]
    fn test_xor(){
        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
             let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();
             let a = AllocatedBit::alloc(&mut cs, Some(*a_val)).unwrap();
             let b = AllocatedBit::alloc(&mut cs, Some(*b_val)).unwrap();
             let c = BooleanWrapper::xor(&mut cs, &Boolean::Is(a), &Boolean::Is(b)).unwrap();
             let cd = BooleanWrapper::xor(&mut cs, &Boolean::Constant(a_val.clone()), &Boolean::Constant(b_val.clone())).unwrap();
             println!("const_xor = {:?}", cd);
             println!("c_xor = {:?}", c);

             assert!(cs.is_satisfied(), "unsatisfied for a = {}, b = {}", a_val, b_val);
             GLOBAL_STORAGE.lock().unwrap().clear_storage();
            }
         }
    }
    #[test]
    fn test_and(){
        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
             let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();
             let a = AllocatedBit::alloc(&mut cs, Some(*a_val)).unwrap();
             let b = AllocatedBit::alloc(&mut cs, Some(*b_val)).unwrap();
             let c = BooleanWrapper::and(&mut cs, &Boolean::Is(a), &Boolean::Is(b)).unwrap();
             let cd = BooleanWrapper::and(&mut cs, &Boolean::Constant(a_val.clone()), &Boolean::Constant(b_val.clone())).unwrap();
             println!("const_and = {:?}", cd);
             println!("c_and = {:?}", c);

             assert!(cs.is_satisfied(), "unsatisfied for a = {}, b = {}", a_val, b_val);
             GLOBAL_STORAGE.lock().unwrap().clear_storage();
             }
        }
    
    }
    #[test]
    fn test_or(){
           for a_val in [false, true].iter() {
               for b_val in [false, true].iter() {
                    let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();
                    let a = AllocatedBit::alloc(&mut cs, Some(*a_val)).unwrap();
                    let b = AllocatedBit::alloc(&mut cs, Some(*b_val)).unwrap();
                    let c = BooleanWrapper::or(&mut cs, &Boolean::Is(a), &Boolean::Is(b)).unwrap();
                    let cd = BooleanWrapper::or(&mut cs, &Boolean::Constant(a_val.clone()), &Boolean::Constant(b_val.clone())).unwrap();
                    println!("const_or = {:?}", cd);
                    println!("c_or = {:?}", c);
   
                    assert!(cs.is_satisfied(), "unsatisfied for a = {}, b = {}", a_val, b_val);
                    GLOBAL_STORAGE.lock().unwrap().clear_storage();
                }
           }
       
    }
    #[test]
    fn test_conditionally(){
           for a_val in [false, true].iter() {
               for b_val in [false, true].iter() {
                    let mut cs = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();
                    let a = AllocatedBit::alloc(&mut cs, Some(*a_val)).unwrap();
                    let b = AllocatedBit::alloc(&mut cs, Some(*b_val)).unwrap();
                    let c = BooleanWrapper::conditionally_select(&mut cs, &Boolean::Constant(true), &Boolean::Is(a), &Boolean::Is(b)).unwrap();
                    let cd = BooleanWrapper::conditionally_select(&mut cs, &Boolean::Constant(false), &Boolean::Constant(a_val.clone()), &Boolean::Constant(b_val.clone())).unwrap();
                    println!("const_select = {:?}", cd);
                    println!("c_select = {:?}", c);
   
                    assert!(cs.is_satisfied(), "unsatisfied for a = {}, b = {}", a_val, b_val);
                    GLOBAL_STORAGE.lock().unwrap().clear_storage();
                }
           }
       
    }
}