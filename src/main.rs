use std::io::prelude::*;

fn read_all<S: AsRef<std::path::Path>>(path: S) -> String {
    let mut content = String::new();
    let mut f = std::fs::File::open(path).unwrap();
    f.read_to_string(&mut content).unwrap();
    content
}

fn main() {
    let fname = std::env::args().nth(1).unwrap_or(String::from("example"));
    let content = read_all(fname);

    let mut registers = HashMap::new();

    let largest = content.lines().map(
        |l| l.parse::<Instruction>().unwrap())
        .filter_map(|i| i.process(&mut registers))
        .max().unwrap();

    let end_largest = registers.values().max().unwrap();

    println!("End Largest value = {}", end_largest);
    println!("Largest value = {}", largest);

}

use std::collections::HashMap;

type Registers = HashMap<String, i32>;

enum ConditionType {
    E,
    NE,
    G,
    GE,
    L,
    LE
}

impl std::str::FromStr for ConditionType {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "==" => Ok(ConditionType::E),
            "!=" => Ok(ConditionType::NE),
            ">" => Ok(ConditionType::G),
            ">=" => Ok(ConditionType::GE),
            "<" => Ok(ConditionType::L),
            "<=" => Ok(ConditionType::LE),
            _ => Err(format!("Invalid token '{}'", s))
        }
    }
}

struct Condition {
    op: ConditionType,
    reg: String,
    value: i32
}

impl ConditionType {
    fn eval(&self, reg_val: i32, value: i32) -> bool {
        match *self {
            ConditionType::E => reg_val == value,
            ConditionType::NE => reg_val != value,
            ConditionType::G => reg_val > value,
            ConditionType::GE => reg_val >= value,
            ConditionType::L => reg_val < value,
            ConditionType::LE => reg_val <= value,
        }
    }
}

impl std::str::FromStr for Condition {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let tokens = s.split(' ').collect::<Vec<_>>();

        Ok(Condition {
            op: tokens[1].parse()?,
            reg: tokens[0].to_string(),
            value: tokens[2].parse().map_err(|e| format!("{:?}", e))?,
        })
    }
}

impl Condition {
    fn eval(&self, registers: &Registers) -> bool {
        self.op.eval(*registers.get(self.reg.as_str()).unwrap_or(&0), self.value)
    }
}

enum Operation {
    Inc(i32),
    Dec(i32)
}

impl std::str::FromStr for Operation {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let tokens = s.splitn(2, ' ').collect::<Vec<_>>();
        let amount = tokens[1].parse().map_err(|e| format!("{:?}", e))?;
        match tokens[0] {
            "inc" => Ok(Operation::Inc(amount)),
            "dec" => Ok(Operation::Dec(amount)),
            t => Err(format!("Invalid operation '{}'", t))
        }
    }
}

impl Operation {
    fn as_sum(&self) -> i32 {
        match *self {
            Operation::Inc(v) => v,
            Operation::Dec(v) => -v
        }
    }
}

struct Action {
    op: Operation,
    reg: String,
}

impl std::str::FromStr for Action {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let tokens = s.splitn(2, ' ').collect::<Vec<_>>();
        if tokens.len() < 2 {
            Err(format!("Invalid Action '{}'", s))
        } else {
            Ok(Action {
                op: tokens[1].parse()?,
                reg: tokens[0].to_string(),
            })
        }
    }
}

impl Action {
    fn apply(&self, registers: &mut Registers) {
        *registers.entry(self.reg.clone()).or_insert(0) += self.op.as_sum();
    }
}

struct Instruction {
    action: Action,
    condition: Condition,
}

impl std::str::FromStr for Instruction {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let components = s.splitn(2, " if ").collect::<Vec<_>>();
        Ok(Self {
            action: components[0].parse()?,
            condition: components[1].parse()?,
        })
    }
}

impl Instruction {
    fn process(&self, registers: &mut Registers) -> Option<i32> {
        self.should(registers)
            .map(|a| {
                a.apply(registers);
                registers[a.reg.as_str()]
            })
    }

    fn should(&self, registers: &Registers) -> Option<&Action> {
        if self.condition.eval(registers) {
            Some(&self.action)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn registers(regs: &[(&str, i32)]) -> Registers {
        regs.into_iter()
            .map(|&(s, v)| (s.to_string(), v))
            .collect::<HashMap<String, i32>>()
    }

    #[test]
    fn conditions() {
        let registers = registers(&[("a", 0), ("d", 3)]);
        assert_eq!(false, "a > 1".parse::<Condition>().unwrap().eval(&registers));
        assert_eq!(true, "a < 1".parse::<Condition>().unwrap().eval(&registers));
        assert_eq!(true, "b == 0".parse::<Condition>().unwrap().eval(&registers));
        assert_eq!(true, "d >= 3".parse::<Condition>().unwrap().eval(&registers));
    }

    #[test]
    fn action() {
        let mut registers = registers(&[("a", 3), ("c", -1), ("d", 1)]);

        "a inc 2".parse::<Action>().unwrap().apply(&mut registers);

        assert_eq!(registers["a"], 5);

        "b dec -10".parse::<Action>().unwrap().apply(&mut registers);

        assert_eq!(registers["b"], 10);

        "c inc -2".parse::<Action>().unwrap().apply(&mut registers);

        assert_eq!(registers["c"], -3);

        "d dec 2".parse::<Action>().unwrap().apply(&mut registers);

        assert_eq!(registers["d"], -1);
    }

    #[test]
    fn instruction() {
        let mut registers = registers(&[("a", 3)]);

        "b inc 5 if a > 1".parse::<Instruction>().unwrap().process(&mut registers);

        assert_eq!(registers["b"], 5);
    }

    static DATA: &'static str = "b inc 5 if a > 1\n\
                                a inc 1 if b < 5\n\
                                c dec -10 if a >= 1\n\
                                c inc -20 if c == 10";

    #[test]
    fn integration() {
        let mut registers = HashMap::new();

        let n = DATA.lines().map(
            |l| l.parse::<Instruction>().unwrap())
            .map(|i| i.process(&mut registers))
            .count();

        assert_eq!(n, 4);
        assert_eq!(-10, registers["c"]);
        assert_eq!(1, registers["a"]);
    }
}
