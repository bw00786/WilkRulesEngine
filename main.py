import os
import json
from datetime import date
import hashlib
from fastapi.responses import RedirectResponse
from pydantic import BaseModel, ValidationError, validator, Field, conint, confloat
from abc import ABC, abstractmethod
from sqlalchemy import text
from sqlalchemy import func  # Add this import
from sqlalchemy import (
    text, 
    Column, 
    Integer, 
    String, 
    JSON, 
    DateTime,
    UniqueConstraint,
    func  # Add this to the existing imports
)
import uuid
from uuid import UUID as PyUUID  # Import Python's UUID type
from sqlalchemy.dialects.postgresql import UUID  # Correct import for PostgreSQL
from datetime import datetime
import asyncio
import logging
import validator
import time
import pandas as pd
from pydantic import BaseModel
from functools import lru_cache
from dateutil.relativedelta import relativedelta
from sqlalchemy import create_engine
from sqlalchemy.orm import sessionmaker
from sqlalchemy.ext.declarative import declarative_base
from sqlalchemy import inspect
from datetime import datetime
from typing import List, Dict, Any, Optional, Tuple, Callable
from contextlib import asynccontextmanager
from fastapi import FastAPI, UploadFile, File, HTTPException, Depends, Request
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import FileResponse
from sqlalchemy.ext.asyncio import AsyncSession, create_async_engine
from sqlalchemy.orm import sessionmaker, declarative_base
from sqlalchemy import Column, Integer, String, JSON, select, UniqueConstraint, Float
from pydantic import BaseModel, ValidationError, validator, Field
import uvicorn
from enum import Enum, auto
import networkx as nx
import matplotlib.pyplot as plt
from redis.asyncio import Redis
from redis.exceptions import RedisError
from dataclasses import dataclass  # Add this line
from collections import deque, defaultdict

# Configure logging
logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s")
logger = logging.getLogger(__name__)

# --------------------------
# Configuration
# --------------------------
DATABASE_URL = "postgresql+asyncpg://user:password@localhost:5433/rules_db"
REDIS_URL = "redis://localhost:6379/0"
#REDIS_URL= "redis://rs-ai-redis.ssnc-corp.cloud/0"
CACHE_TTL = 300  # 5 minutes
MAX_POOL_SIZE = int(os.getenv('POOL_SIZE', 20))
MAX_OVERFLOW = int(os.getenv('MAX_OVERFLOW', 5))
DATABASE_PORT = int(os.getenv('DATABASE_PORT', 54321))


# Create SQLAlchemy async engine
engine = create_async_engine(
  DATABASE_URL,
  pool_size=MAX_POOL_SIZE,
  max_overflow=MAX_OVERFLOW
)

# Create an async session factory
AsyncSessionLocal = sessionmaker(engine, class_=AsyncSession, expire_on_commit=False)


# Define the Base for SQLAlchemy models
Base = declarative_base()

# --------------------------
# Redis Setup
# --------------------------
async def get_redis():
    redis = Redis.from_url(REDIS_URL, decode_responses=True)
    try:
        yield redis
    finally:
        await redis.close()

def sha256_hash(data: str) -> str:
    """Generate SHA-256 hash for audit records"""
    return hashlib.sha256(data.encode()).hexdigest()   

class RuleEngineCore:
    def __init__(self):
        self.plugins = []
        self.conflict_resolvers = []
        self.action_validators = []
        
    def register_plugin(self, plugin):
        self.plugins.append(plugin)
        self.conflict_resolvers.extend(plugin.get_conflict_resolvers())
        self.action_validators.extend(plugin.get_action_validators())   


# Add these new classes for Rete implementation
class AlphaNode:
    """Represents a condition on a single fact attribute"""
    def __init__(self, condition):
        self.condition = condition  # {'field': {'operator': value}}
        self.successors = []
        
    def matches(self, facts):
        try:
            field = next(iter(self.condition))
            cond = self.condition[field]
            
            # Handle special refRule case
            if field == 'refRule':
                return True # Let BetaNodes handle this

            op = cond.get('operator')
            val = cond.get('value')
            
            if not op or not val:
                return False

            fact_val = facts[field]
            return self._compare_values(op, fact_val, val)
        
        except (KeyError, TypeError) as e:
            logger.error(f"Invalid condition format: {self.condition}")
            return False

    def _compare_values(self, op, fact_val, condition_val):
        # Implementation of comparison logic
        try:
            if op == "==": return fact_val == condition_val
            elif op == "!=": return fact_val != condition_val
            elif op == ">=": return float(fact_val) >= float(condition_val)
            elif op == "<=": return float(fact_val) <= float(condition_val)
            elif op == ">": return float(fact_val) > float(condition_val)
            elif op == "<": return float(fact_val) < float(condition_val)
            elif op == "in": return fact_val in condition_val
            elif op == "not_in": return fact_val not in condition_val
            return False
        except (TypeError,  ValueError):
            return False    

class BetaNode:
    """Beta node for joining conditions"""
    def __init__(self, operator):
        self.operator = operator  # 'and' or 'or'
        self.successors = []
        self.conditions = []
        self.referenced_rules = []  # To store references to other rules
    def add_reference(self, rule_name):
        """Add a referenced rule dependency"""
        self.referenced_rules.append(rule_name)    
        

class ReteNetwork:
    """Main Rete network implementation"""
    def __init__(self):
        self.alpha_nodes = {}
        self.beta_nodes = []
        self.productions = {}
        self.working_memory = set()
        self.rule_dependencies = defaultdict(set)  # Track rule dependencies

    def _check_join_conditions(self, beta_node, facts):
    ##Check if the beta node's join conditions are satisfied by the facts
        if beta_node.operator == 'and':
            # For AND nodes, all conditions must be met
            for condition in beta_node.conditions:
                if not self._evaluate_condition(condition, facts):
                    return False
            return True
        elif beta_node.operator == 'or':
           # For OR nodes, at least one condition must be met
           if not beta_node.conditions:
              return False
           for condition in beta_node.conditions:
               if self._evaluate_condition(condition, facts):
                  return True
           return False
        return False    
    
    def _evaluate_condition(self, condition, facts):
        """Evaluate a single condition against facts"""
        if isinstance(condition, dict):
            for field, cond_def in condition.items():
                # Skip refRule conditions as they're handled separately
                if field == 'refRule':
                   continue
                
                # Get the value from facts
                if field not in facts:
                    return False
                
                fact_value = facts[field]
            
                # Get operator and expected value
                operator = cond_def.get('operator')
                expected_value = cond_def.get('value')
            
                # Evaluate based on operator
                if operator == '==':
                    if fact_value != expected_value:
                        return False
                elif operator == '!=':
                    if fact_value == expected_value:
                         return False
                elif operator == '>':
                    if not (fact_value > expected_value):
                       return False
                elif operator == '>=':
                    if not (fact_value >= expected_value):
                        return False
                elif operator == '<':
                    if not (fact_value < expected_value):
                        return False
                elif operator == '<=':
                     if not (fact_value <= expected_value):
                         return False
            # Add more operators as needed
    
        return True
    
    def _check_standard_conditions(self, beta_node):
        """Check standard conditions for a beta node"""
        # This method should match the logic in _check_beta_conditions
        # but focusing only on standard (non-refRule) conditions
        if beta_node.operator == 'and':
             return all(self._evaluate_condition(cond, self.working_memory) 
                       for cond in beta_node.conditions)
        elif beta_node.operator == 'or':
             return any(self._evaluate_condition(cond, self.working_memory) 
                    for cond in beta_node.conditions)
        return False

    def _activate(self, node, facts, activated, agenda):
        """Propagate activation through the network with agenda"""
        if node not in activated:
            activated.add(node)
            agenda.append(node)

        for successor in node.successors:
            if isinstance(successor, BetaNode):
                # Check join conditions for BetaNode
                if self._check_join_conditions(successor, facts):
                    self._activate(successor, facts, activated, agenda)
            else:
                # Propagate to other nodes
                self._activate(successor, facts, activated, agenda)   
               

    
    def add_rule(self, rule):
        """Compile rule conditions into Rete nodes"""
        # Create production node for actions
        prod_node = ProductionNode(rule)
        self.productions[rule['name']] = prod_node
        
        # Build condition tree
        self._build_condition_tree(rule['conditions'], prod_node)

    def _build_condition_tree(self, conditions, parent_node):
        """Recursively build Rete nodes from conditions"""
        if 'and' in conditions:
            beta = BetaNode('and')
            for cond in conditions['and']:
                self._process_condition(cond, beta)
            beta.successors.append(parent_node)
            self.beta_nodes.append(beta)
        elif 'or' in conditions:
            beta = BetaNode('or')
            for cond in conditions['or']:
                self._process_condition(cond, beta)
            beta.successors.append(parent_node)
            self.beta_nodes.append(beta)
        else:
            self._process_condition(conditions, parent_node)

    def _process_condition(self, condition, parent_node):
        """Create alpha nodes for simple conditions or handle nested logic"""
        if isinstance(condition, dict):
            # Handle logical operators recursively
            if 'and' in condition or 'or' in condition:
                self._build_condition_tree(condition, parent_node)
                return
            # Handle rule references
            if 'refRule' in condition:
                ref_alpha = AlphaNode({'refRule': condition['refRule']})
                ref_alpha.successors.append(parent_node)
                self.alpha_nodes[str(condition)] = ref_alpha
                # Add to rule dependencies
                if isinstance(parent_node, ProductionNode):
                    self.rule_dependencies[parent_node.rule['name']].add(condition['refRule'])
                elif isinstance(parent_node, BetaNode):
                     parent_node.referenced_rules.append(condition['refRule'])
                return
                # Handle implicit AND for multiple fields
                if len(condition) > 1:
                   beta = BetaNode('and')
                   for field, cond_def in condition.items():
                      self._process_condition({field: cond_def}, beta)
                   beta.successors.append(parent_node)
                   self.beta_nodes.append(beta)
            else:
                   for field, cond_def in condition.items():
                        # Create AlphaNode for each field
                        alpha_key = f"{field}_{cond_def['operator']}_{cond_def['value']}"
                        if alpha_key not in self.alpha_nodes:
                           self.alpha_nodes[alpha_key] = AlphaNode({field: cond_def})
                        self.alpha_nodes[alpha_key].successors.append(parent_node)
                        # Add condition to parent node if it's a BetaNode
                        if isinstance(parent_node, BetaNode):
                           parent_node.conditions.append({field: cond_def})
        elif isinstance(condition, list):
            # Handle implicit AND for lists
            beta = BetaNode('and')
            for cond in condition:
                self._process_condition(cond, beta)
            beta.successors.append(parent_node)
            self.beta_nodes.append(beta) 

    def process_facts(self, facts):
        """evaluate facts through the Rete network with proper refRule handling"""
        # Store facts in working memory
        self.working_memory = facts  
        activated = set()
        agenda = deque()

        # Phase 1: Alpha node processing
        for alpha in self.alpha_nodes.values():
            if alpha.matches(facts):
                self._activate(alpha, facts, activated, agenda)

        # Phase 2: Beta node processing with refRule support
        while agenda:
            current_node = agenda.popleft()

            if isinstance(current_node, BetaNode):
                # Handle rule references for beta nodes
                if self._check_beta_conditions(current_node, activated):
                    for successor in current_node.successors:
                        if successor not in activated:
                            self._activate(successor, facts, activated, agenda)
                           

            elif isinstance(current_node, ProductionNode):
                # Add to final results if all dependencies are met
                if self._check_rule_dependencies(current_node.rule, activated):
                    activated.add(current_node)

        return [p.rule for p in activated if isinstance(p, ProductionNode)]
    
  
    
    def _check_beta_conditions(self, beta_node, activated):
        """Check both regular conditions and rule references"""
        # Check standard conditions
        conditions_met = self._check_standard_conditions(beta_node)
        
        # Check rule references
        ref_rules_met = all(
            any(p.rule['name'] == ref_rule for p in activated 
                if isinstance(p, ProductionNode))
            for ref_rule in beta_node.referenced_rules
        )

        if beta_node.operator == 'and':
            return conditions_met and ref_rules_met
        elif beta_node.operator == 'or':
            return conditions_met or ref_rules_met
        return False

    def _check_rule_dependencies(self, rule, activated):
        """Verify all dependencies for a production rule"""
        return all(
            any(p.rule['name'] == dep for p in activated 
                if isinstance(p, ProductionNode))
            for dep in self.rule_dependencies[rule['name']]
        )

    
                
class ProductionNode:
    """Represents a rule's actions when conditions are met"""
    def __init__(self, rule):
        self.rule = rule
        ##self.actions = rule['actions']    
        self.successors = []  # Even though typically production nodes are terminal, 
                             # adding this for consistency    

# Define Action first
class Action(BaseModel):
    type: str  # Remove the alias to accept 'type' from input data
    parameters: Optional[Dict[str, Any]] = None
    key: Optional[str] = None
    value: Optional[Any] = None

    @validator('parameters')
    def validate_parameters(cls, v, values):
        action_type = values.get('type')
        if action_type == 'schedule_distribution':
            if 'end_type' in v and 'end_date' in v:
                raise ValueError("Cannot specify both end_type and end_date")
        return v        

class Conflict(BaseModel):
    type: str
    message: str
    actions: List[Action]
    resolution: Optional[List[Action]] = None  



    def _resolve_conflict_group(self, actions: List[Dict]):
        resolution = max(actions, key=lambda x: x['priority'])
        conflict_detail = {
            'type': 'priority_based_resolution',
            'message': f"Selected action from rule {resolution['rule_name']} "
                      f"due to higher priority ({resolution['priority']})",
            'conflicting_actions': actions,
            'selected_action': resolution,
            'resolution_criteria': 'highest_priority'
        }
        return resolution, conflict_detail    
    
class ConflictResolver(ABC):
    @abstractmethod
    def detect_conflicts(self, actions: List[Action]) -> List[Conflict]:
        pass

class RMDConflictResolver:
    def __init__(self):
        self.current_year = date.today().year
        self.penalty_rate = 0.50  # IRS penalty for insufficient RMD
        
        # IRS Uniform Lifetime Table (simplified)
        self.rmd_table = {
            72: 27.4,
            73: 26.5,
            74: 25.5,
            75: 24.6,
            # ... continue with full table values
        }

    def calculate_rmd(self, account):
        """Calculate required minimum distribution"""
        age = self.current_year - account.owner.birth_year
        divisor = self.rmd_table.get(age, 1.0)  # Default to full balance if beyond table
        return account.balance / divisor

    def detect_conflicts(self, accounts):
        conflicts = []
        for account in accounts:
            if account.account_type in ['IRA', '401K', 'SEP IRA'] and account.owner.age >= 72:
                required = self.calculate_rmd(account)
                distributed = sum(t.amount for t in account.distributions 
                              if t.year == self.current_year)
                
                if distributed < required:
                    conflicts.append({
                        'account': account,
                        'shortfall': required - distributed,
                        'deadline': date(self.current_year, 12, 31),
                        'penalty': (required - distributed) * self.penalty_rate
                    })
        return conflicts

    def resolve_conflicts(self, conflicts):
        resolutions = []
        for conflict in conflicts:
            # Create automatic distribution for shortfall
            resolution = {
                'action': 'AUTO_DISTRIBUTE',
                'account_id': conflict['account'].id,
                'amount': conflict['shortfall'],
                'deadline': conflict['deadline'],
                'penalty_warning': conflict['penalty'],
                'description': f"RMD shortfall distribution of ${conflict['shortfall']:.2f}"
            }
            resolutions.append(resolution)
            
            # If past deadline, add penalty transaction
            if date.today() > conflict['deadline']:
                resolutions.append({
                    'action': 'APPLY_PENALTY',
                    'account_id': conflict['account'].id,
                    'amount': conflict['penalty'],
                    'description': "50% IRS penalty for late RMD"
                })
                
        return resolutions
    
    def resolve(self, actions):
        # IRS priority: Initial RMD > Uniform Table > Annual Recalculation
        ordered_types = [
            "initial_rmd_73_2025",
            "apply_uniform_life_table", 
            "subsequent_annual_rmd"
        ]
        return sorted(actions, 
            key=lambda x: ordered_types.index(x['parameters']['rmd_type']))

    def execute(self, financial_data):
        conflicts = self.detect_conflicts(financial_data.retirement_accounts)
        return self.resolve_conflicts(conflicts)  
    
# --------------------------
# Condition Handler (Move before DomainPlugin)
# --------------------------
class ConditionHandler(ABC):
    @abstractmethod
    def evaluate(self, facts: Dict, params: Dict) -> bool:
        pass            

class DomainPlugin:
    def get_conflict_resolvers(self) -> List[ConflictResolver]:
        raise NotImplementedError
        
    def get_action_validators(self) -> List[Callable]: 
        raise NotImplementedError
        
    def get_custom_conditions(self) -> Dict[str, ConditionHandler]:
        raise NotImplementedError   

class ConditionHandler(ABC):
    @abstractmethod
    def evaluate(self, facts: Dict, params: Dict) -> bool:
        pass            

class RuleDependencyType(Enum):
    """Enum to represent different types of rule dependencies"""
    DIRECT = auto()
    CONTEXTUAL = auto()
    OPTIONAL = auto()
    CRITICAL = auto()

@dataclass
class RuleDependencyMetadata:
    """Comprehensive metadata for rule dependencies"""
    name: str
    context: str
    weight: float = 1.0
    execution_time: float = 0.0
    complexity: float = 0.0
    dependency_type: RuleDependencyType = RuleDependencyType.DIRECT
    last_executed: Optional[datetime] = None
    execution_count: int = 0
    failure_count: int = 0

class RuleValidator:
    """Comprehensive rule validator with semantic and content validation"""
    
    def __init__(self, db: AsyncSession):
        self.db = db
        self.logger = logging.getLogger(__name__)
    
    async def validate_rule_set(self, rules: List[Dict[str, Any]]) -> Tuple[bool, List[Dict[str, Any]]]:
        """
        Validate a complete set of rules including cross-references and cycles
        
        Args:
            rules: List of rule dictionaries
            
        Returns:
            Tuple[bool, List[Dict]]: (is_valid, validation_errors)
        """
        if not rules:
            return False, [{"error": "No rules provided"}]
            
        # Validate individual rules first
        all_errors = []
        for rule in rules:
            valid, error_dicts = await self.validate_rule(rule, rules)
            if not valid:
                for error in error_dicts:
                    # Add this check to handle both dictionary and string errors
                    if isinstance(error, dict) and 'loc' in error:
                         loc = "->".join(map(str, error['loc']))
                         all_errors.append({
                             "row": 0,
                             "rule_name": rule.get('name', 'Unknown'),
                             "error_type": "Validation Error",
                              "error_message": f"{loc}: {error['msg']}"
                         })
                    else:
                    # Handle string errors or incorrectly formatted dict errors
                        all_errors.append({
                            "row": 0,
                            "rule_name": rule.get('name', 'Unknown'),
                            "error_type": "Validation Error",
                            "error_message": str(error)
                       })     
        
        if all_errors:
            return False, all_errors
            
        # Check for cyclic dependencies
        try:
            evaluator = ContextualRuleEvaluator(self.db)
            context = rules[0].get('context', 'default')
            await evaluator.prepare_rule_graph(rules, context)
        except ValueError as e:
            if "Cyclic dependencies" in str(e):
                return False, [{"error": f"Dependency cycle detected: {str(e)}"}]
            raise
            
        # All validations passed
        return True, []
    
    async def validate_rule(self, rule: Dict[str, Any], all_rules: List[Dict[str, Any]]) -> Tuple[bool, List[Dict]]:
        """
        Validate a single rule semantically
        
        Args:
            rule: Rule dictionary to validate
            all_rules: All rules for cross-reference validation
            
        Returns:
            Tuple[bool, List[str]]: (is_valid, error_messages)
        """
        errors = []
        
        # Check basic structure using Pydantic
        try:
            rule_obj = RuleCreate(**rule)
        except ValidationError as e:
            errors.extend(e.errors())  # Pydantic errors are already dicts with 'loc' and 'msg'
        
        # Validate condition structure and references
        condition_errors = self._validate_conditions(rule.get('conditions', {}), all_rules)
        errors.extend(condition_errors)
        
        # Validate actions
        action_errors = self._validate_actions(rule.get('actions', []))
        errors.extend(action_errors)
        
        # Check for duplicate rule names
        duplicate = await self._check_duplicate_rule(rule.get('name', ''), rule.get('context', 'default'))
        if duplicate:
            errors.append({'loc': ('name',), 'msg': f"Rule name already exists in context '{rule.get('context')}'"})
        
        return (len(errors) == 0, errors)
    
    def _validate_conditions(self, conditions: Dict[str, Any], all_rules: List[Dict[str, Any]]) -> List[Dict]:
        """Validate condition structure and references"""
        errors = []
        
        # Handle empty conditions
        if not conditions:
           errors.append({'loc': ('conditions',), 'msg': "Conditions cannot be empty"})
           return errors  # Return dict-based errors, not strings
            
        # Check for logical operator structure
        if not any(op in conditions for op in ['and', 'or', 'refRule']):
            # Single condition check
            if not self._is_valid_condition_format(conditions):
                errors.append({'loc': ('conditions',), 'msg': "Invalid condition format. Expected operators like 'and', 'or', or field conditions."})
        
        # Check referenced rules
        ref_rules = self._extract_referenced_rules(conditions)
        for ref_rule in ref_rules:
            if not any(r.get('name') == ref_rule for r in all_rules):
                errors.append({'loc': ('conditions', 'refRule'), 'msg': f"Referenced rule '{ref_rule}' does not exist"})
        
        # Validate logical structure
        if 'and' in conditions:
            if not isinstance(conditions['and'], list) or not conditions['and']:
                errors.append("'and' operator must have a non-empty list of conditions")
            else:
                for subcond in conditions['and']:
                    errors.extend(self._validate_conditions(subcond, all_rules))
                    
        if 'or' in conditions:
            if not isinstance(conditions['or'], list) or not conditions['or']:
                errors.append("'or' operator must have a non-empty list of conditions")
            else:
                for subcond in conditions['or']:
                    errors.extend(self._validate_conditions(subcond, all_rules))
        
        # Validate date comparisons
        if 'date_comparison' in conditions:
            date_comp = conditions['date_comparison']
            if not all(k in date_comp for k in ['field', 'operator']):
                errors.append("Date comparison requires 'field' and 'operator'")
            if date_comp.get('operator') not in ['before', 'after', 'within_years']:
                errors.append(f"Invalid date comparison operator: {date_comp.get('operator')}")
        
        return errors
    
    def _is_valid_condition_format(self, condition: Dict[str, Any]) -> bool:
        """Check if a leaf condition has valid format"""
        if not isinstance(condition, dict):
            return False
            
        # Each condition should be field -> {operator, value} format
        for field, details in condition.items():
            if not isinstance(details, dict):
                return False
            if 'operator' not in details or 'value' not in details:
                return False
                
            # Validate operator
            op = details.get('operator')
            if op not in ['==', '!=', '>=', '<=', '>', '<', 'in', 'not_in']:
                return False
                
        return True
        
    def _extract_referenced_rules(self, conditions: Dict[str, Any]) -> List[str]:
        """Extract all referenced rule names from conditions"""
        ref_rules = []
        
        if isinstance(conditions, dict):
            if 'refRule' in conditions:
                ref_rules.append(conditions['refRule'])
                
            for key, value in conditions.items():
                if isinstance(value, dict):
                    ref_rules.extend(self._extract_referenced_rules(value))
                elif isinstance(value, list):
                    for item in value:
                        if isinstance(item, dict):
                            ref_rules.extend(self._extract_referenced_rules(item))
                            
        return ref_rules
    
    def _validate_actions(self, actions: List[Dict[str, Any]]) -> List[Dict]:
        """Validate action structure and required parameters"""
        errors = []
        
        for idx, action in enumerate(actions):
            if 'type' not in action:
                errors.append({'loc': ('actions', idx), 'msg': "Action missing 'type' field"})
            action_type = action.get('type')
            params = action.get('parameters', {})
            
            if not action_type:
                errors.append("Action missing required 'type' field")
                continue
                
            # Type-specific validation
            if action_type == 'schedule_distribution':
                amount_keys = [key for key in params if 'amount' in key.lower()]
                if not amount_keys:
                    logger.info(f"checking for amount in {params}")
                    errors.append("'schedule_distribution' action requires a parameter containing 'amount'")
                
                # Check end_type and end_date are not both specified
                if 'end_type' in params and 'end_date' in params:
                    errors.append("Cannot specify both 'end_type' and 'end_date' in schedule_distribution")
                    
            elif action_type == 'calculate_rmd':
                if 'rmd_type' not in params:
                    errors.append("'calculate_rmd' action requires 'rmd_type' parameter")
            
            # Add more action-specific validations here
            
        return errors
        
    async def _check_duplicate_rule(self, rule_name: str, context: str) -> bool:
        """Check if a rule with the same name exists in the context"""
        if not rule_name:
            return False
            
        query = select(RuleModel).where(
            (func.lower(RuleModel.name) == rule_name.lower()) & 
            (func.lower(RuleModel.context) == context.lower())
        )
        
        result = await self.db.execute(query)
        return result.scalar() is not None
        
    async def test_evaluate_rule(self, rule: Dict[str, Any], sample_facts: Dict[str, Any]) -> Dict[str, Any]:
        """Test evaluate a rule against sample facts to verify it works"""
        try:
            evaluator = ContextualRuleEvaluator(self.db)
            
            # Create a temporary list with just this rule
            temp_rule_list = [rule]
            result = await evaluator._evaluate_rule(
                rule=rule,
                facts=sample_facts,
                all_rules=temp_rule_list,
                cache=EvaluationCache()
            )
            
            return {
                "can_evaluate": True,
                "conditions_met": result['conditions_met'],
                "actions": result.get('actions', []) if result['conditions_met'] else [],
                "matched_conditions": result.get('matched_conditions', [])
            }
        except Exception as e:
            return {
                "can_evaluate": False,
                "error": str(e)
            }    

class DateUtils:
    @staticmethod
    def calculate_age(dob: datetime) -> float:
        today = datetime.today()
        return today.year - dob.year - ((today.month, today.day) < (dob.month, dob.day))

    @staticmethod
    def parse_date(date_str: str, default: datetime = None) -> Optional[datetime]:
        try:
            return datetime.strptime(date_str, "%Y-%m-%d")
        except (ValueError, TypeError):
            return default

    @staticmethod
    def years_between(start: datetime, end: datetime) -> float:
        return relativedelta(end, start).years    

class RuleDependencyGraph:
    def __init__(self):
        """
        Create a sophisticated rule dependency graph using NetworkX
        """
        self.graph = nx.DiGraph()
        self.rule_metadata: Dict[str, RuleDependencyMetadata] = {}

    @lru_cache(maxsize=128)
    def has_cycles(self, context: str) -> bool:
        """Memoized cycle check per context"""
        try:
            cycles = list(nx.simple_cycles(self.graph))
            return len(cycles) > 0
        except nx.NetworkXNoCycle:
            return False    
        
    def detect_cycles(self, max_depth=10) -> list:
        """Use cached cycle detection"""
        if not self.has_cycles(self.context):
            return []
            
        # Only calculate full cycles if needed
        return [c for c in nx.simple_cycles(self.graph) if len(c) <= max_depth]    

    def add_rule(self, rule: Dict[str, Any]):
        """
        Add a rule to the dependency graph with comprehensive metadata
        """
        rule_name = rule.get('name')
        rule_context = rule.get('context', 'default')
        
        # Create or update rule metadata
        metadata = RuleDependencyMetadata(
            name=rule_name,
            context=rule_context,
            weight=rule.get('priority', 1.0) / 10.0,  # Normalize priority
            complexity=self._calculate_rule_complexity(rule)
        )
        self.rule_metadata[rule_name] = metadata
        
        # Add node to graph
        self.graph.add_node(rule_name, metadata=metadata)

    def add_dependency(
        self, 
        source_rule: str, 
        target_rule: str, 
        dependency_type: RuleDependencyType = RuleDependencyType.DIRECT
    ):
        """
        Add a weighted, typed dependency between rules
        """
        if source_rule not in self.graph.nodes or target_rule not in self.graph.nodes:
            raise ValueError(f"Rules {source_rule} or {target_rule} not in graph")
        
        weight = self._calculate_dependency_weight(
            self.rule_metadata[source_rule], 
            self.rule_metadata[target_rule]
        )
        
        self.graph.add_edge(
            source_rule, 
            target_rule, 
            weight=weight, 
            type=dependency_type
        )

    def _calculate_rule_complexity(self, rule: Dict[str, Any]) -> float:
        """
        Calculate rule complexity based on conditions and actions
        """
        conditions = rule.get('conditions', {})
        actions = rule.get('actions', [])
        
        # Basic complexity calculation
        condition_complexity = self._count_nested_conditions(conditions)
        action_complexity = len(actions)
        
        return (condition_complexity * 0.6) + (action_complexity * 0.4)

    def _count_nested_conditions(self, conditions: Dict[str, Any]) -> int:
        """
        Recursively count nested conditions
        """
        if isinstance(conditions, dict):
            if 'and' in conditions or 'or' in conditions:
                return 1 + sum(
                    self._count_nested_conditions(cond) 
                    for cond in conditions.get('and', []) + conditions.get('or', [])
                )
            return 1
        return 0

    def _calculate_dependency_weight(
        self, 
        source_metadata: RuleDependencyMetadata, 
        target_metadata: RuleDependencyMetadata
    ) -> float:
        """
        Calculate dependency weight based on rule metadata
        """
        context_match = (source_metadata.context == target_metadata.context)
        
        return (
            source_metadata.weight * 
            target_metadata.weight * 
            (1.5 if context_match else 1.0)
        )

    def detect_cycles(self, max_depth: int = 10) -> List[List[str]]:
        """
        Detect cycles in the dependency graph with configurable depth
        """
        try:
            cycles = list(nx.simple_cycles(self.graph))
            return [cycle for cycle in cycles if len(cycle) <= max_depth]
        except nx.NetworkXNoCycle:
            return []

    def optimize_execution_order(self) -> List[str]:
        """
        Optimize rule execution order using topological sorting with priority-based ordering within generations
        """
        try:
            generations = nx.topological_generations(self.graph)
            sorted_generations = []
            for gen in generations:
                # Sort each generation by descending priority (ascending due to negative sign)
                sorted_gen = sorted(
                    gen,
                    key=lambda x: -self.rule_metadata[x].weight
                )
                sorted_generations.append(sorted_gen)
            # Flatten the generations into a single list
            optimized_order = [node for gen in sorted_generations for node in gen]
            return optimized_order
        except nx.NetworkXUnfeasible:
            return self._handle_cyclic_graph()

    def _handle_cyclic_graph(self) -> List[str]:
        """
        Handle cyclic graphs by breaking cycles and then applying priority-based topological sort
        """
        cycles = self.detect_cycles()
        working_graph = self.graph.copy()

        for cycle in cycles:
            weakest_edge = min(
                ((u, v) for u, v in zip(cycle, cycle[1:] + [cycle[0]])),
                key=lambda edge: self.graph[edge[0]][edge[1]].get('weight', 1.0)
            )
            working_graph.remove_edge(*weakest_edge)

        try:
            generations = nx.topological_generations(working_graph)
            sorted_generations = []
            for gen in generations:
                sorted_gen = sorted(
                    gen,
                    key=lambda x: -self.rule_metadata[x].weight
                )
                sorted_generations.append(sorted_gen)
            optimized_order = [node for gen in sorted_generations for node in gen]
            return optimized_order
        except nx.NetworkXUnfeasible:
            return list(working_graph.nodes())

    def visualize_dependency_graph(self, output_path: str = '/tmp/rule_dependency_graph.png'):
        """
        Generate a visual representation of the rule dependency graph
        """
        plt.figure(figsize=(12, 8))
        pos = nx.spring_layout(self.graph, k=0.5, iterations=50)
        
        # Draw nodes
        nx.draw_networkx_nodes(
            self.graph, 
            pos, 
            node_color='lightblue', 
            node_size=500
        )
        
        # Draw edges
        nx.draw_networkx_edges(
            self.graph, 
            pos, 
            edge_color='gray',
            arrows=True
        )
        
        # Draw labels
        nx.draw_networkx_labels(self.graph, pos, font_size=8)
        
        plt.title("Rule Dependency Graph")
        plt.axis('off')
        plt.tight_layout()
        plt.savefig(output_path)
        plt.close()
        
        return output_path

    def export_dependency_graph(self) -> Dict[str, Any]:
        """
        Export rule dependency graph as a structured JSON
        """
        graph_data = {
            'nodes': [],
            'edges': [],
            'metadata': {}
        }
        
        # Export nodes
        for node in self.graph.nodes():
            metadata = self.rule_metadata.get(node)
            graph_data['nodes'].append({
                'id': node,
                'context': metadata.context,
                'weight': metadata.weight,
                'complexity': metadata.complexity
            })
            
            graph_data['metadata'][node] = {
                'execution_time': metadata.execution_time,
                'execution_count': metadata.execution_count,
                'last_executed': metadata.last_executed.isoformat() if metadata.last_executed else None
            }
        
        # Export edges
        for source, target, data in self.graph.edges(data=True):
            graph_data['edges'].append({
                'source': source,
                'target': target,
                'weight': data.get('weight', 1.0),
                'type': data.get('type', 'DIRECT').name
            })
        
        return graph_data    

class EvaluateRulesRequest(BaseModel):
    context: str
    facts: Dict[str, Any]
    
    @validator('context')
    def validate_context(cls, v):
        if not v.strip():
            raise ValueError("Context cannot be empty")
        return v       

class ExcelRuleUploader:
    def __init__(self, db: AsyncSession):
        self.db = db
        self.logger = logging.getLogger(__name__)

    

    async def validate_excel_structure(self, file_path: str) -> List[Dict[str, Any]]:
        def parse_value(val):
            try:
                return int(val)
            except ValueError:
                try:
                    return float(val)
                except ValueError:
                    return val

        try:
                df = pd.read_excel(file_path)
                required_columns = ['context', 'name', 'priority', 'description', 'conditions', 'actions']
        
                if missing := [col for col in required_columns if col not in df.columns]:
                   raise ValueError(f"Missing columns: {', '.join(missing)}")

                rules = []
                for idx, row in df.iterrows():
                    excel_row_num = idx + 2  # Account for header row
                    try:
                       # SINGLE PARSE with error context
                       raw_actions = row['actions']
                      
                       try:
                          actions = json.loads(raw_actions) if isinstance(raw_actions, str) else raw_actions
                          logger.debug(f"Validated actions for row {excel_row_num}: {json.dumps(actions, indent=2)}") 

                       except json.JSONDecodeError as e:
                           raise ValueError(f"Invalid JSON in actions (Row {excel_row_num}): {str(e)} Action: {actions}")

                       # Process conditions
                       raw_conditions = row['conditions']
                       try:
                           conditions = json.loads(
                           raw_conditions,
                           parse_float=parse_value,
                           parse_int=parse_value
                           )
                       except json.JSONDecodeError as e:
                            raise ValueError(f"Invalid JSON in conditions (Row {excel_row_num}): {str(e)} Conditions: {conditions}")    

                       # Validate individual actions first

                       if not isinstance(actions, list):
                          raise ValueError(f"Actions must be an array in row {excel_row_num}")
                       for action_idx, action in enumerate(actions, 1):
                           if not isinstance(action, dict):
                                raise ValueError(f"Action {action_idx} must be an object in row {excel_row_num}")
                           if 'type' not in action:
                              raise ValueError(f"Action {action_idx} missing 'type' in row {excel_row_num}")
                           if 'parameters' not in action:
                              raise ValueError(f"Action {action_idx} missing 'parameters' in row {excel_row_num}")

                       # Now parse conditions with numeric handling
                       conditions = json.loads(
                          row['conditions'],
                          parse_float=parse_value,
                          parse_int=parse_value
                       )

                       rule = {
                           'context': str(row['context']),
                           'name': str(row['name']),
                           'priority': int(row['priority']),
                           'description': str(row['description']),
                           'conditions': conditions,
                           'actions': actions
                       }

                       # Validate with Pydantic
                       RuleCreate(**rule)
                       rules.append(rule)

                    except Exception as e:
                       logger.error(f"Error in Excel row {excel_row_num} (ID: {row.get('id', 'N/A')}): {str(e)}")
                       raise HTTPException(400, detail=f"Row {excel_row_num}: {str(e)}")

                return rules

        except Exception as e:
                logger.error(f"Excel processing failed: {str(e)}", exc_info=True)
                raise HTTPException(400, detail=f"File validation failed: {str(e)}")
        finally:
                if os.path.exists(file_path):
                    try: os.remove(file_path)
                    except Exception as e: logger.warning(f"Cleanup error: {str(e)}")    

# --------------------------
# Pydantic Models
# --------------------------

class EvaluationCache:
        def __init__(self):
            self.rule_results = {}
            self.condition_cache = {}

        def rule_cache_key(self, rule_name: str, facts: dict) -> str:
            # Use more efficient hashing for large fact dictionaries
            facts_hash = xxhash.xxh64(json.dumps(facts, sort_keys=True)).hexdigest()
            return f"{rule_name}-{facts_hash}"

class ActionConflictResolver:
    def __init__(self):
        self.conflict_rules = [
            self._detect_scheduling_conflicts,
            self._detect_calculation_conflicts
           
        ]

    def resolve_conflicts(self, all_actions: List[Dict]) -> Tuple[List[Dict], List[Dict]]:
        """Main entry point for conflict resolution"""
        action_groups = self._group_actions_by_type(all_actions)
        resolved = []
        conflicts = []
        
        for action_type, actions in action_groups.items():
            if len(actions) > 1:
                group_resolved, group_conflicts = self._resolve_action_group(actions)
                resolved.extend(group_resolved)
                conflicts.extend(group_conflicts)
            else:
                resolved.extend(actions)
                
        return resolved, conflicts

    def _resolve_action_group(self, actions: List[Dict]) -> Tuple[List[Dict], List[Dict]]:
        """Resolve conflicts within an action type group"""
        # First check for hard conflicts
        for check in self.conflict_rules:
            conflict_found, resolved = check(actions)
            if conflict_found:
                return resolved, [conflict_found]
        
        # Then sort by priority/exec order
        return self._prioritize_actions(actions), []

    def _detect_scheduling_conflicts(self, actions: List[Dict]) -> Tuple[Optional[Dict], List[Dict]]:
        """Detect conflicting distribution schedules"""
        scheduling_actions = [a for a in actions if a["action"]["type"] == "schedule_distribution"]
        
        if len(scheduling_actions) > 1:
            conflict_details = {
                "type": "scheduling_conflict",
                "message": "Multiple scheduling actions found",
                "actions": scheduling_actions
            }
            # Automatically select the highest priority one
            resolved = [max(scheduling_actions, key=lambda x: x["priority"])]
            return conflict_details, resolved
            
        return None, actions

    def _detect_calculation_conflicts(self, actions: List[Dict]) -> Tuple[Optional[Dict], List[Dict]]:
        """Detect conflicting calculation methods"""
        calc_actions = [a for a in actions if "calculate" in a["action"]["type"]]
        
        if len(calc_actions) > 1:
            conflict_details = {
                "type": "calculation_conflict",
                "message": "Multiple calculation methods specified",
                "actions": calc_actions
            }
            return conflict_details, [self._select_calculation_action(calc_actions)]
            
        return None, actions

    def _select_calculation_action(self, actions: List[Dict]) -> Dict:
        """Select calculation action based on priority and specificity"""
        return max(actions, key=lambda x: (
            x["priority"], 
            x["action"]["parameters"].get("complexity", 0)
        ))

    def _group_actions_by_type(self, actions: List[Dict]) -> Dict[str, List[Dict]]:
        """Group actions by their type and target"""
        groups = defaultdict(list)
        for action in actions:
            key = f"{action['action']['type']}-{action['action'].get('target')}"
            groups[key].append(action)
        return groups

    def _prioritize_actions(self, actions: List[Dict]) -> List[Dict]:
        """Sort actions by priority and execution order"""
        return sorted(
            actions,
            key=lambda x: (-x["priority"], x["exec_order"]),
        )        
    
class EnhancedActionConflictResolver(ActionConflictResolver):
    def resolve_conflicts(self, all_actions: List[Dict]) -> Tuple[List[Dict], List[Dict]]:
        resolved = []
        conflicts = []
        
        for action_type, actions in self._group_actions_by_type(all_actions).items():
            if len(actions) > 1:
                resolution, conflict = self._resolve_conflict_group(actions)
                resolved.append(resolution)
                conflicts.append(conflict)
            else:
                resolved.extend(actions)
                
        return resolved, conflicts

    def _resolve_conflict_group(self, actions: List[Dict]):
        resolution = max(actions, key=lambda x: x['priority'])
        conflict_detail = {
            'type': 'priority_based_resolution',
            'message': f"Selected action from rule {resolution['rule_name']} "
                      f"due to higher priority ({resolution['priority']})",
            'conflicting_actions': actions,
            'selected_action': resolution,
            'resolution_criteria': 'highest_priority'
        }
        return resolution, conflict_detail    
    
class RuleNamingService:
    CONTEXT_MAP = {
        'rmd': 'RetirementDistribution',
        'espp': 'EmployeeStockPlan',
        'hsa': 'HealthSavingsAccount'
    }

    @classmethod
    def get_full_name(cls, rule: Dict) -> str:
        base_name = rule['name'].replace(' ', '')
        context = cls.CONTEXT_MAP.get(rule['context'], 'General')
        return f"{context}_{base_name}_v{rule.get('version', 1)}"


      
class ContextualRuleEvaluator:
    def __init__(self, db: AsyncSession):
        self.db = db
        self.dependency_graph = RuleDependencyGraph()
        self.logger = logging.getLogger(__name__)


    
        
    async def prepare_rule_graph(self, rules: List[Dict[str, Any]], context: str):
        """
        Prepare a comprehensive rule dependency graph and return execution order
    
         Args:
        rules: List of rule dictionaries
        context: Context for the rules
    
         Returns:
        List[str]: Optimized execution order of rule names
    
         Raises:
            ValueError: If cyclic dependencies are detected
        """
         # Reset graph for new context
        self.dependency_graph = RuleDependencyGraph()
    
        # Add rules to graph
        for rule in rules:
            self.dependency_graph.add_rule(rule)
    
        # Analyze and add dependencies
        for rule in rules:
           await self._analyze_rule_dependencies(rule, rules)
    
        # Detect cycles
        cycles = self.dependency_graph.detect_cycles()
        if cycles:
          self.logger.warning(f"Detected dependency cycles: {cycles}")
          raise ValueError(f"Cyclic dependencies detected in rules: {cycles}")
    
        # Get optimized execution order
        return self.dependency_graph.optimize_execution_order()

    async def _analyze_rule_dependencies(self, rule: Dict[str, Any], all_rules: List[Dict[str, Any]]):
        """
        Analyze and add rule dependencies dynamically
        """
        def _find_referenced_rules(conditions: Dict[str, Any]):
            """Recursively find referenced rules"""
            referenced = []
            if isinstance(conditions, dict):
                if 'refRule' in conditions:
                    referenced.append(conditions['refRule'])
                
                for value in conditions.values():
                    if isinstance(value, (dict, list)):
                        referenced.extend(_find_referenced_rules(value))
            
            elif isinstance(conditions, list):
                for item in conditions:
                    referenced.extend(_find_referenced_rules(item))
            
            return referenced

        # Find referenced rules in conditions
        referenced_rules = _find_referenced_rules(rule.get('conditions', {}))
        
        for ref_rule_name in referenced_rules:
            # Find the referenced rule
            ref_rule = next((r for r in all_rules if r['name'] == ref_rule_name), None)
            
            if ref_rule:
                dependency_type = (
                    RuleDependencyType.CRITICAL if ref_rule.get('priority', 0) > 7 
                    else RuleDependencyType.OPTIONAL
                )
                
                try:
                    self.dependency_graph.add_dependency(
                        rule['name'], 
                        ref_rule_name, 
                        dependency_type
                    )
                except ValueError as e:
                    self.logger.warning(f"Dependency error: {e}")

    async def evaluate_rules(
        self, 
        rules: List[Dict[str, Any]], 
        facts: Dict[str, Any], 
        context: str
    ):
        """
        Evaluate rules with advanced dependency management
        """
        # Prepare rule graph and get optimal execution order
        execution_order = await self.prepare_rule_graph(rules, context)
        
        # Create ordered rules list based on execution order
        ordered_rules = [rule for rule in rules if rule['name'] in execution_order]
    
        # Initialize request-scoped cache
        request_cache = EvaluationCache()
       
        
        # Parallel rule evaluation with dependency awareness
        async def evaluate_rule_with_tracking(rule, all_rules, cache):
            start_time = datetime.now()
            try:
                # Existing rule evaluation logic
                result = await self._evaluate_rule(
                    rule, 
                    facts, 
                    all_rules,  # Add all_rules
                    cache    # Add cache
                )
                
                # Update rule metadata
                return result
            except Exception as e:
                logger.error(f"Rule {rule['name']} evaluation failed: {e}")
                return {
                    "rule_name": rule.get('name', 'unknown'),
                    "error": str(e),
                    "conditions_met": False,
                    "execution_time": time.time() - start_time
                }

        # Create tasks with required parameters
        tasks = [
            evaluate_rule_with_tracking(
               rule,           # Current rule
               rules,          # Full list of context rules
               request_cache   # Request-scoped cache
            )
            for rule in ordered_rules
        ]
    
        evaluation_results = await asyncio.gather(*tasks)
    
        # Optional: Visualize rule dependency graph
        graph_visualization_path = self.dependency_graph.visualize_dependency_graph()
    
        return {
           'results': evaluation_results,
           'execution_order': execution_order,
           'dependency_graph': self.dependency_graph.export_dependency_graph(),
           'graph_visualization': graph_visualization_path
        }

        
       

    async def _evaluate_rule(self, rule: dict, facts: dict, all_rules: List[Dict], cache: EvaluationCache) -> Dict[str, Any]:
        cache_key = cache.rule_cache_key(rule['name'], facts)
    
        if cache_key in cache.rule_results:
           return cache.rule_results[cache_key]
        
        start_time = time.time()  # Initialize timer at start
        try:
           # Evaluate conditions with proper async handling
            conditions_met = await evaluate_conditions(
               rule['conditions'],
               facts,
               rule.get('context', 'default'),
               all_rules
            )

           # Get matched conditions with cache
            matched_conditions = await self._find_matched_conditions(
                rule['conditions'],
                facts,
                all_rules,
                cache  # Add cache parameter here
            )

            result = {
               "rule_name": rule['name'],
               "conditions_met": conditions_met,
               "conditions_evaluated": rule['conditions'],
               "actions": rule['actions'] if conditions_met else [],
               "matched_conditions": matched_conditions,
               "execution_time": time.time() - start_time
            }

            cache.rule_results[cache_key] = result
            return result

        except Exception as e:
            logger.error(f"Error evaluating rule {rule.get('name')}: {str(e)}")
            return {
                "rule_name": rule.get('name', 'unknown'),
                "error": str(e),
                "conditions_met": False
            }
  
    async def _find_matched_conditions(self, conditions: Dict, facts: Dict, all_rules: List, cache: EvaluationCache) -> List[Dict]:
        """Recursively find which conditions matched with cache"""
        matched = []
        if 'and' in conditions:
          for cond in conditions['and']:
            if await self._condition_matches(cond, facts, all_rules, cache):
                matched.append(cond)
        elif 'or' in conditions:
            for cond in conditions['or']:
                if await self._condition_matches(cond, facts, all_rules, cache):
                    matched.append(cond)
        return matched

    async def _condition_matches(self, condition: Dict, facts: Dict, all_rules: List, cache: EvaluationCache) -> bool:
        """Check if a single condition matches facts"""
        if 'refRule' in condition:
               return await self._handle_rule_reference(
                  condition['refRule'], 
                  facts, 
                  all_rules,
                  cache  # Add cache parameter
                )

        for field, condition_def in condition.items():
            if not isinstance(condition_def, dict):
                continue

            op = condition_def.get('operator')
            val = condition_def.get('value')
            fact_val = facts.get(field)

            # Handle cases where 'value' might be a reference to another fact
            if isinstance(val, dict) and 'use_fact' in val:
                val = facts.get(val['use_fact'])

            try:
                if op == "==": return fact_val == val
                elif op == "!=": return fact_val != val
                elif op == "in": return fact_val in val if isinstance(val, (list, tuple)) else False
                elif op == "not_in": return fact_val not in val if isinstance(val, (list, tuple)) else True
                elif op in [">=", "<=", ">", "<"]:
                    try:
                        # Attempt to parse both values as dates
                        fact_date = DateUtils.parse_date(str(fact_val))
                        condition_date = DateUtils.parse_date(str(val))
                        if fact_date and condition_date:
                            logger.info(f"This is a date comparision: ${condition_date} and fact_date is = {fact_date}")
                            if op == ">=": return fact_date >= condition_date
                            elif op == "<=": return fact_date <= condition_date
                            elif op == ">": return fact_date > condition_date
                            elif op == "<": return fact_date < condition_date
                    except (TypeError, ValueError):
                        # If date parsing fails, attempt numerical comparison
                        try:
                            fact_num = float(fact_val)
                            condition_num = float(val)
                            if op == ">=": return fact_num >= condition_num
                            elif op == "<=": return fact_num <= condition_num
                            elif op == ">": return fact_num > condition_num
                            elif op == "<": return fact_num < condition_num
                        except (TypeError, ValueError):
                            return False # Neither date nor number

                return False # Operator not handled
            except Exception as e:
                logger.error(f"Error in _condition_matches for field '{field}': {e}")
                return False

               
      
    # In ContextualRuleEvaluator class
    async def _handle_rule_reference(self, rule_name: str, facts: Dict, all_rules: List, cache: EvaluationCache) -> bool:
       """Handle references to other rules"""
       ref_rule = next((r for r in all_rules if r['name'] == rule_name), None)
       if not ref_rule:
           return False
    
       result = await self._evaluate_rule(ref_rule, facts, all_rules, cache)
       return result['conditions_met']

    def _get_matched_conditions(self, conditions: Dict, facts: Dict) -> List[Dict]:
        """Helper to identify which specific conditions matched"""
        matched = []
    
        if 'and' in conditions:
            for cond in conditions['and']:
                if self._condition_matches(cond, facts):
                   matched.append(cond)
                
        elif 'or' in conditions:
            for cond in conditions['or']:
                if self._condition_matches(cond, facts):
                    matched.append(cond)
                
        return matched
  
# Modified ContextualRuleEvaluator using Rete
class ReteRuleEvaluator(ContextualRuleEvaluator):
    def __init__(self, db: AsyncSession):
        super().__init__(db)
        self.rete_network = ReteNetwork()
        self.initialized = False

    async def initialize_network(self, rules):
        """Build Rete network from rules"""
        for rule in rules:
            self.rete_network.add_rule(rule)
        self.initialized = True

    async def evaluate_rules(self, rules: List[Dict], facts: Dict, context: str):
        """Evaluate using Rete network"""
        if not self.initialized:
            await self.initialize_network(rules)
            
        # Process facts through Rete network
        logger.info("processing facts via Rete network")
        matched_rules = self.rete_network.process_facts(facts)
        
        # Collect results
        return [{
            'rule_name': rule['name'],
            'conditions_met': True,
            'actions': rule['actions'],
            'matched_conditions': self._get_matched_conditions(rule, facts)
        } for rule in matched_rules]

    def _get_matched_conditions(self, rule, facts):
        """Determine which conditions were matched (simplified)"""
        # Implementation would trace through Rete activation path
        return [{"condition": "implement matched conditions tracking"}]
# Updated Rule Model to support enhanced metadata
class EnhancedRuleModel(BaseModel):
    name: str
    context: str
    priority: int = 5
    conditions: Dict[str, Any]
    actions: List[Dict[str, Any]]
    metadata: Dict[str, Any] = Field(default_factory=dict)    


class RuleCreate(BaseModel):
    context: str = Field(default="default")
    name: str
    priority: int = Field(5, ge=1, le=10)
    description: str = Field(default="No description provided")
    conditions: Dict[str, Any]
    actions: List[Action]

    @validator('actions', pre=True)
    def wrap_single_action(cls, v):
        if isinstance(v, dict):
            return [v]
        return v
    

    @validator('conditions')
    def validate_conditions(cls, v):
        """Basic validation of conditions structure"""
        if not v:
            raise ValueError("Conditions cannot be empty")
            
        # Check for logical operators or field conditions
        if not any(op in v for op in ['and', 'or', 'refRule']):
            # Must be a field condition with proper structure
            if not any(isinstance(details, dict) and 'operator' in details for details in v.values()):
                raise ValueError("Invalid condition format - must use logical operators or field conditions")
                
        # Validate 'and'/'or' structures
        if 'and' in v and (not isinstance(v['and'], list) or not v['and']):
            raise ValueError("'and' operator must have a non-empty list of conditions")
            
        if 'or' in v and (not isinstance(v['or'], list) or not v['or']):
            raise ValueError("'or' operator must have a non-empty list of conditions")
            
        return v   


# --------------------------
# Database Models
# --------------------------
class RuleModel(Base):
    __tablename__ = "rules3456717_9"
    id = Column(Integer, primary_key=True, index=True)
    context = Column(String, index=True) 
    name = Column(String, index=True)
    priority = Column(Integer, default=5, nullable=False)
    description = Column(String,  nullable=True)
    conditions = Column(JSON, nullable=False)
    actions = Column(JSON, nullable=False)
    
   ## __table_args__ = (UniqueConstraint('context', 'name',  name='uq_rule_name_context'),)

# --------------------------
# Cache Management
# --------------------------
class RuleCache:
    def __init__(self, redis: Redis):
        self.redis = redis
        self.lock = asyncio.Lock()
        self.cache_key = "rules:all"
        self.timestamp_key = "rules:last_updated"

    async def get_rules(self) -> List[Dict]:
        """Retrieve rules from Redis cache"""
        try:
            cached_data = await self.redis.get(self.cache_key)
            return json.loads(cached_data) if cached_data else []
        except RedisError as e:
            logger.error(f"Redis error: {str(e)}")
            return []

    async def is_cache_stale(self) -> bool:
        """Check if cache needs refresh"""
        try:
            last_update = await self.redis.get(self.timestamp_key)
            if not last_update:
                return True
            last_db_update = datetime.fromisoformat(last_update)
            return (datetime.now() - last_db_update).seconds > CACHE_TTL
        except (RedisError, ValueError):
            return True

    async def refresh(self, db: AsyncSession):
        """Refresh cache from database"""
        async with self.lock:
            try:
                result = await db.execute(
                    select(RuleModel).order_by(RuleModel.priority.asc())
                )
                rules = result.scalars().all()
                
                serialized_rules = json.dumps([
                    {
                        "id": rule.id,
                        "context": rule.context,
                        "name": rule.name,
                        "priority": rule.priority,
                        "description": rule.description,  # Fixed typo here
                        "conditions": rule.conditions,
                        "actions": rule.actions
                    } for rule in rules
                ])
                
                async with self.redis.pipeline() as pipe:
                    await pipe.set(self.cache_key, serialized_rules)
                    await pipe.set(self.timestamp_key, datetime.now().isoformat())
                    await pipe.execute()
                
                logger.info(f"Refreshed Redis cache with {len(rules)} rules")
            except Exception as e:
                logger.error(f"Cache refresh failed: {str(e)}")
                raise

# Add to your database models
class UploadReport(Base):
    __tablename__ = "upload_reports2"
    
    id = Column(UUID, primary_key=True, default=uuid.uuid4)
    filename = Column(String)
    upload_timestamp = Column(DateTime, default=datetime.now)
    processing_time = Column(Float)
    stats = Column(JSON)  # {success_rate: 0.95, total_rules: 20, successful: 19, failed: 1}
    errors = Column(JSON)  # List of error objects
    context = Column(String)            

    
    @validator('beneficiary_allocation')
    def validate_allocation(cls, v):
        if not (0 <= v <= 100):
            raise ValueError("Allocation must be 0-100%")
        return v   

class MerkleNode:
    def __init__(self, hash: str):
        self.hash = hash
        self.left = None
        self.right = None

class MerkleTree:
    def __init__(self):
        self.root = None
        self.leaves = []

    def add_block(self, data: dict):
        """Add new audit record to the tree"""
        data_str = json.dumps(data, sort_keys=True)
        leaf_hash = sha256_hash(data_str)
        self.leaves.append(MerkleNode(leaf_hash))
        self._build_tree()

    def _build_tree(self):
        """Build Merkle tree from leaves"""
        nodes = self.leaves.copy()
        while len(nodes) > 1:
            new_level = []
            for i in range(0, len(nodes), 2):
                left = nodes[i]
                right = nodes[i+1] if i+1 < len(nodes) else nodes[i]
                combined = left.hash + right.hash
                parent_hash = sha256_hash(combined)
                parent = MerkleNode(parent_hash)
                parent.left, parent.right = left, right
                new_level.append(parent)
            nodes = new_level
        self.root = nodes[0] if nodes else None

    def get_root_hash(self) -> str:
        """Get current root hash for audit verification"""
        return self.root.hash if self.root else ""

class AuditLogger:
    def log_evaluation(self, facts: Dict, rules: List, results: Dict):
        audit_record = {
            "timestamp": datetime.utcnow().isoformat(),
            "fact_hash": self._generate_hash(facts),
            "rule_versions": {r['name']: r['version'] for r in rules},
            "evaluation_id": uuid.uuid4(),
            "results": {
                "triggered_rules": results['evaluation_results'],
                "conflicts": results['action_conflicts'],
                "final_actions": results['resolved_actions']
            },
            "system_state": {
                "rule_engine_version": "2.3.1",
                "irs_table_version": "2024-02",
                "dependency_graph_hash": self._generate_hash(results['dependency_graph'])
            }
        }
        self._store_to_immutable_db(audit_record)

class ImmutableAuditStore:
    def __init__(self):
        self.merkle_tree = MerkleTree()
        self.ledger = []
        self.last_hash = "0" * 64  # Genesis block hash

    def _write_to_worm_storage(self, block: dict):
        """Write Once Read Many (WORM) storage implementation"""
        self.ledger.append(block)
        self.last_hash = block['data_hash']

    def store_record(self, record: dict):
        block = {
            "previous_hash": self.last_hash,
            "data_hash": sha256_hash(json.dumps(record)),
            "timestamp": datetime.utcnow().isoformat(),
            "data": record
        }
        self.merkle_tree.add_block(block)
        self._write_to_worm_storage(block)

    def verify_integrity(self) -> bool:
        """Verify blockchain-style integrity"""
        for i in range(1, len(self.ledger)):
            current = self.ledger[i]
            previous = self.ledger[i-1]
            
            if current['previous_hash'] != previous['data_hash']:
                return False
                
            calculated_hash = sha256_hash(json.dumps(current['data']))
            if current['data_hash'] != calculated_hash:
                return False
                
        return True

# --------------------------
# FastAPI Setup
# --------------------------
@asynccontextmanager
async def lifespan(app: FastAPI):
    # Initialize audit storage once at startup
    app.state.audit_store = ImmutableAuditStore()
    async with engine.begin() as conn:
        # Add UUID extension if using PostgreSQL
        await conn.execute(text("CREATE EXTENSION IF NOT EXISTS \"uuid-ossp\""))
        await conn.run_sync(Base.metadata.create_all)
        # Check if tables exist first
        logger.info("chaecking for table existence")
        if not await conn.run_sync(lambda sync_conn: inspect(sync_conn).has_table("rules3456717_9")):
            await conn.run_sync(Base.metadata.create_all)
    yield

    logger.info("Final audit root hash: %s", app.state.audit_store.merkle_tree.get_root_hash())

    
    # Rest of your lifespan code...
    redis = Redis.from_url(REDIS_URL, decode_responses=True)
    rule_cache = RuleCache(redis)
    async with AsyncSessionLocal() as db:
        await rule_cache.refresh(db)
    yield
    await redis.close()


def check_and_update_columns(conn):
    # CORRECTED TABLE NAME TO MATCH MODEL
    table_name = "rules3456717_9"
    
    inspector = inspect(conn)
    
    # Check if table exists first
    if not inspector.has_table(table_name):
        return
        
    columns = inspector.get_columns(table_name)
    
    # Check for priority column
    if not any(col['name'] == 'priority' for col in columns):
        # CORRECTED TABLE NAME IN SQL
        conn.execute(text(
            f"ALTER TABLE {table_name} ADD COLUMN priority INTEGER NOT NULL DEFAULT 5"
        ))
        conn.commit()

app = FastAPI(lifespan=lifespan)

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["POST", "GET"],  # Explicitly list allowed methods,
    allow_headers=["*"],
)

# --------------------------
# Dependency Injection
# --------------------------
async def get_db():
    async with AsyncSessionLocal() as session:
        try:
            yield session
        except Exception as e:
            await session.rollback()
            raise
        finally:
            await session.close()

async def get_cache(redis: Redis = Depends(get_redis)) -> RuleCache:
    return RuleCache(redis)
    

# --------------------------
# Rule Evaluation Logic (FIXED)
# --------------------------
async def evaluate_condition(
    condition: Dict[str, Any],
    facts: Dict[str, Any],
    context: str,
    all_rules: List[Dict],
    depth: int = 0
) -> bool:
    if depth > 10:
        raise RecursionError("Maximum condition nesting depth exceeded")
    if not condition:
         return True
    if "refRule" in condition:
        rule_name = condition["refRule"]
        referenced_rule = next((r for r in all_rules if r["name"] == rule_name), None)
        if referenced_rule:
            return await evaluate_conditions(
                referenced_rule["conditions"],
                facts,
                context,
                all_rules,
                depth + 1
            )
        return False

    if "and" in condition:
        results = await asyncio.gather(*[
            evaluate_conditions(c, facts, context, all_rules, depth + 1)
            for c in condition["and"]
        ])
        return all(results)

    if "or" in condition:
        results = await asyncio.gather(*[
            evaluate_conditions(c, facts, context, all_rules, depth + 1)
            for c in condition["or"]
        ])
        return any(results)

    for field, condition_def in condition.items():
        if not isinstance(condition_def, dict):
            # Skip non-dict condition definitions
            continue
            
        try:
            op = condition_def.get("operator")
            val = condition_def.get("value")
            
            if op is None or val is None:
                continue
        except (KeyError, AttributeError):
            continue

        # Get fact value and handle missing facts
        fact_val = facts.get(field)
        
        # Type safety for comparisons
        try:
            if op == "==":
                return fact_val == val
            elif op == "!=":
                return fact_val != val
            elif op == ">=":
                # Type check for comparison operators
                if fact_val is None or val is None:
                    return False
                return float(fact_val) >= float(val)
            elif op == "<=":
                if fact_val is None or val is None:
                    return False
                return float(fact_val) <= float(val)
            elif op == ">":
                if fact_val is None or val is None:
                    return False
                return float(fact_val) > float(val)
            elif op == "<":
                if fact_val is None or val is None:
                    return False
                return float(fact_val) < float(val)
            elif op == "in":
                if fact_val is None or not isinstance(val, (list, tuple)):
                    return False
                return fact_val in val
            elif op == "not_in":
                if fact_val is None or not isinstance(val, (list, tuple)):
                    return False
                return fact_val not in val
        except (TypeError, ValueError) as e:
            # Log the error but don't crash
            logger.warning(f"Type error in comparison: {fact_val} {op} {val}. Error: {str(e)}")
            return False

    return False

async def evaluate_conditions(
    conditions: Dict[str, Any],
    facts: Dict[str, Any],
    context: str,
    all_rules: List[Dict],
    depth: int = 0
    
) -> bool:
    if 'date_comparison' in conditions:
        return await _handle_date_comparison(conditions, facts)
    return await evaluate_condition(conditions, facts, context, all_rules, depth)

# In _handle_date_comparison
async def _handle_date_comparison(condition: Dict, facts: Dict) -> bool:
    date_field = condition['date_comparison']['field']
    operator = condition['date_comparison']['operator']
    comparison_date = DateUtils.parse_date(condition['date_comparison']['value'])
    
    fact_date_str = facts.get(date_field)
    fact_date = DateUtils.parse_date(fact_date_str)
    
    if not fact_date or not comparison_date:
        return False
    
    if operator == "before":
        return fact_date < comparison_date
    elif operator == "after":
        return fact_date > comparison_date
    elif operator == "within_years":
        years = condition['date_comparison']['years']
        return DateUtils.years_between(fact_date, comparison_date) <= years
    return False
# --------------------------
# API Endpoints
# --------------------------
# Sample Excel Template Generation Endpoint
@app.get("/rule_upload_template")
async def generate_rule_upload_template():
    """
    Generate an Excel template for rule uploads
    """
    # Create a sample DataFrame with expected columns
    sample_data = pd.DataFrame([
        {
            'name': 'Sample Rule',
            'priority': 5,
            'description': 'A sample rule for demonstration',
            'conditions': json.dumps({
                'and': [
                    {'participant_status': {'operator': '==', 'value': 'Active'}},
                    {'age': {'operator': '>=', 'value': 73}}
                ]
            }),
            'actions': json.dumps([
                {
                    'type': 'calculate_rmd',
                    'target': 'system',
                    'parameters': {
                        'rmd_type': 'initial_rmd_73_2025'
                    }
                }
            ])
        }
    ])
    
    # Generate Excel file
    output_path = '/tmp/rule_upload_template.xlsx'
    sample_data.to_excel(output_path, index=False)
    
    # Return file for download
    return FileResponse(
        output_path, 
        media_type='application/vnd.openxmlformats-officedocument.spreadsheetml.sheet',
        filename='rule_upload_template.xlsx'
    )    
class evaluate_rules(BaseModel):
    context: str
    facts: Dict[str, Any]

# evaulate rules
@app.post("/evaluate_rules/")
async def evaluate_rules(
    evaluate_request: EvaluateRulesRequest,  # Renamed parameter
    request: Request,  # Injected FastAPI Request
    db: AsyncSession = Depends(get_db),
    cache: RuleCache = Depends(get_cache)
):
    try:
        context = evaluate_request.context  # Use renamed parameter
        facts = evaluate_request.facts

        cached_rules = await cache.get_rules()
        context_rules = [rule for rule in cached_rules if rule['context'] == context]

        # Create request-specific evaluation cache
       
        if not context_rules:
            if await cache.is_cache_stale():
                async with AsyncSessionLocal() as refresh_db:
                    await cache.refresh(refresh_db)
                cached_rules = await cache.get_rules()
                # To case-insensitive comparison:
                context_rules = [
                    rule for rule in cached_rules 
                    if rule.get('context', '').lower() == context.lower()
]
            if not context_rules:
                raise HTTPException(status_code=404, detail=f"No rules found for context: {context}")

        evaluator = ReteRuleEvaluator(db)
        await evaluator.initialize_network(context_rules)
        execution_order = await evaluator.prepare_rule_graph(context_rules, context)
        ordered_rules = [rule for rule in context_rules if rule['name'] in execution_order]


        # Evaluate using Rete
        logger.info("evaluating using Rete network")
        evaluation_results = await evaluator.evaluate_rules(context_rules, facts, context)

        # Conflict resolution for actions
        all_actions = []
        for result, rule in zip(evaluation_results, ordered_rules):
            if result['conditions_met']:
                for action in result.get('actions', []):
                    all_actions.append({
                        'action': action,
                        'priority': rule['priority'],
                        'rule_name': rule['name'],
                        'exec_order': execution_order.index(rule['name'])
                    })

        # New conflict resolution implementation:
        resolver = ActionConflictResolver()
        resolved_actions, action_conflicts = resolver.resolve_conflicts(all_actions)

        audit_record = {
             "timestamp": datetime.utcnow().isoformat(),
             "user": "system",
             "action": "Rules Evaluation",
             "details": {
                   "context": evaluate_request.context,  # Changed from request.context
                   "rules_applied": [r['rule_name'] for r in evaluation_results]  # Ensure correct key
    }
}
        
        # Store in audit chain
        request.app.state.audit_store.store_record(audit_record)


        return {
            "context": context,
            "input_facts": facts,
            "evaluation_results": [
                {
                    "rule": result['rule_name'],
                    "priority": rule['priority'],
                    "conditions_met": result['conditions_met'],
                    "actions_triggered": result.get('actions', []),
                    "matched_conditions": result.get('matched_conditions', []),
                    "execution_time_ms": round(result.get('execution_time', 0) * 1000, 2),
                    "audit_trace_id": audit_record["timestamp"],
                    "error": result.get('error')
                }
                for result in evaluation_results
            ],
            "resolved_actions": resolved_actions,
            "action_conflicts": action_conflicts,
            "execution_order": execution_order,
            "dependency_graph": evaluator.dependency_graph.export_dependency_graph()
           
        }

    except HTTPException:
        raise
    except Exception as e:
        logger.error(f"Evaluation error: {str(e)}", exc_info=True)
        # Store error in audit log
        error_record = {
            "timestamp": datetime.utcnow().isoformat(),
            "user": "system",
            "action": "Evaluation Error",
            "details": str(e)
        }
        request.app.state.audit_store.store_record(error_record)
        raise HTTPException(status_code=500, detail=str(e))
    

@app.post("/upload_rules/")
async def upload_rules(
    file: UploadFile = File(...),
    db: AsyncSession = Depends(get_db),
    cache: RuleCache = Depends(get_cache),
    sample_facts: Optional[Dict[str, Any]] = None
):
    """
    Upload rules via JSON or Excel file with enhanced validation and cycle detection.
    
    Args:
        file: Uploaded file (Excel or JSON)
        db: Database session
        cache: Rule cache instance
        sample_facts: Optional sample facts to test rule evaluation
        
    Returns:
        dict: Success message with count of uploaded rules
        
    Raises:
        HTTPException: For validation errors or processing failures
    """
    logger.info(f"processing file {file}")
    start_time = time.time()
    report_id = uuid.uuid4()
    try:
        # Determine file type
        filename = file.filename.lower()
        logger.info(f"Processing uploaded file: {filename}")
        
        # Create temporary file
        temp_path = f"/tmp/{filename}"
        with open(temp_path, "wb") as buffer:
            buffer.write(await file.read())
        
        # Process based on file extension
        uploader = ExcelRuleUploader(db)
        
        if filename.endswith(('.xlsx', '.xls')):
            rules_data = await uploader.validate_excel_structure(temp_path)
        elif filename.endswith('.json'):
            with open(temp_path, 'r') as f:
                rules_data = json.load(f)
                if not isinstance(rules_data, (list, dict)):
                    raise HTTPException(
                        status_code=400,
                        detail="JSON must be an array of rules or a single rule object"
                    )
        else:
            raise HTTPException(
                status_code=400, 
                detail="Unsupported file type. Use .xlsx, .xls, or .json"
            )
        
        # Clean up temporary file
        if os.path.exists(temp_path):
            os.remove(temp_path)
        
        # Convert single rule to list format if needed
        if isinstance(rules_data, dict):
            rules_data = [rules_data]
            
        if not rules_data:
            raise HTTPException(
                status_code=400,
                detail="No valid rules found in uploaded file"
            )
        
        # Enhanced validation with our new validator
        validator = RuleValidator(db)
        is_valid, validation_errors = await validator.validate_rule_set(rules_data)
        
        if not is_valid:
            return {
                "status": "error",
                "message": "Rule validation failed",
                "validation_errors": validation_errors
            }
        
        # Test evaluation if sample facts are provided
        test_results = []
        if sample_facts:
            for rule in rules_data:
                eval_result = await validator.test_evaluate_rule(rule, sample_facts)
                test_results.append({
                    "rule_name": rule.get('name'),
                    "evaluation_result": eval_result
                })

        
        # Process in transaction
        try:
            
                new_rule_count = 0
                for rule_data in rules_data:
                    # Add new rule (validation already confirmed no duplicates)
                    db.add(RuleModel(
                        context=rule_data.get('context', 'default'),
                        name=rule_data['name'],
                        priority=rule_data.get('priority', 5),
                        description=rule_data.get('description', ''),
                        conditions=rule_data['conditions'],
                        actions=rule_data['actions']
                    ))
                    new_rule_count += 1
              
                await db.commit()
                logger.info(f"Successfully added {new_rule_count} new rules")

             
                # New: Track processing metrics
                processing_time = time.time() - start_time
                success_rate = new_rule_count / len(rules_data) if rules_data else 0  

                # Create report record
                report = UploadReport(
                   id=report_id,
                   filename=file.filename,
                   processing_time=processing_time,
                   stats={
                       "success_rate": success_rate,
                       "total_rules_processed": len(rules_data),
                       "successful_uploads": new_rule_count,
                       "failed_uploads": len(rules_data) - new_rule_count
                    },
                     errors=validation_errors,
                     context=rules_data[0].get('context', 'default') if rules_data else 'default'
                )
        
                db.add(report)
                await db.commit()
            
               # Refresh cache with new independent session
                async with AsyncSessionLocal() as refresh_db:
                   await cache.refresh(refresh_db)
            
                return {
                    "report_id": report_id,
                    "filename": file.filename,
                    "processing_time": processing_time,
                    "stats": report.stats,
                    "errors": validation_errors,
                    "test_results": test_results
                   
                }
                
            
        except Exception as e:
           # Track error in report
            await db.rollback()
            error_report = UploadReport(
               id=report_id,
               filename=file.filename,
               processing_time=time.time() - start_time,
               stats={"success_rate": 0, "total_rules_processed": 0, "successful_uploads": 0, "failed_uploads": 0},
               errors=[{"error_type": "system", "error_message": str(e)}],
               context="error"
            )
            db.add(error_report)
            await db.commit()
            logger.error(f"Database error during rule upload: {str(e)}", exc_info=True)
            raise HTTPException(
                status_code=500,
                detail="Failed to save rules to database"
            )
            
    except HTTPException:
        # Re-raise existing HTTP exceptions
        logger.error(" Re-raise existing HTTP exceptions")
        raise
        
    except json.JSONDecodeError:
        logger.error("Invalid JSON format")
        raise HTTPException(
            status_code=400,
            detail="Invalid JSON format"
        )
        
    except Exception as e:
        logger.error(f"Unexpected error during rule upload: {str(e)}", exc_info=True)
        raise HTTPException(
            status_code=500,
            detail="An unexpected error occurred during rule upload"
        )    
@app.get("/upload_rules/", include_in_schema=False)
async def upload_rules_help():
    return {
        "message": "Use POST to upload rules",
        "expected_format": {
            "file": "Excel/JSON file with rules",
            "sample_facts": "(Optional) Test facts payload"
        }
    }
"""@app.get("/audit/integrity")
async def verify_audit_integrity(app: FastAPI = Depends(get_app)):
    return {
        "is_valid": app.state.audit_store.verify_integrity(),
        "root_hash": app.state.audit_store.merkle_tree.get_root_hash(),
        "block_count": len(app.state.audit_store.ledger)
    }"""
@app.get("/rules/upload-reports/")
async def get_recent_reports(db: AsyncSession = Depends(get_db)):
    result = await db.execute(
        select(UploadReport)
        .order_by(UploadReport.upload_timestamp.desc())
        .limit(10)
    )
    return result.scalars().all()

# Modified upload endpoint
@app.post("/rules/upload-report/")
async def upload_rules(
    file: UploadFile = File(...),
    db: AsyncSession = Depends(get_db),
    cache: RuleCache = Depends(get_cache)
):
    start_time = time.time()
    report_id = uuid.uuid4()
    
    try:
        # Existing processing logic...
        
        # New: Track processing metrics
        processing_time = time.time() - start_time
        success_rate = new_rule_count / len(rules_data) if rules_data else 0
        
        # Create report record
        report = UploadReport(
            id=report_id,
            filename=file.filename,
            processing_time=processing_time,
            stats={
                "success_rate": success_rate,
                "total_rules_processed": len(rules_data),
                "successful_uploads": new_rule_count,
                "failed_uploads": len(rules_data) - new_rule_count
            },
            errors=validation_errors,
            context=rules_data[0].get('context', 'default') if rules_data else 'default'
        )
        
        db.add(report)
        await db.commit()

        return {
            "report_id": report_id,
            "filename": file.filename,
            "processing_time": processing_time,
            "stats": report.stats,
            "errors": validation_errors,
            "test_results": test_results
        }

    except Exception as e:
        # Track error in report
        await db.rollback()
        error_report = UploadReport(
            id=report_id,
            filename=file.filename,
            processing_time=time.time() - start_time,
            stats={"success_rate": 0, "total_rules_processed": 0, "successful_uploads": 0, "failed_uploads": 0},
            errors=[{"error_type": "system", "error_message": str(e)}],
            context="error"
        )
        db.add(error_report)
        await db.commit()
        raise    

@app.get("/rules/upload-report/{report_id}")
async def get_report(report_id: PyUUID, db: AsyncSession = Depends(get_db)):
    query = select(UploadReport).where(UploadReport.id == report_id)
    result = await db.execute(query)
    report = result.scalars().first()
    if not report:
        raise HTTPException(status_code=404, detail="Report not found")
    return report    
    
@app.post("/evaluate/")
async def evaluate_facts(
    facts: Dict[str, Any],
    context: str,
    cache: RuleCache = Depends(get_cache)
):
    try:
        # Get rules from Redis cache
        rules = await cache.get_rules()
        
        # Log received facts for debugging
        logger.info(f"Evaluating facts: {json.dumps(facts)}")
        
        # Fallback to database if cache is empty
        if not rules and await cache.is_cache_stale():
            async with AsyncSessionLocal() as db:
                await cache.refresh(db)
            rules = await cache.get_rules()

        results = []
        for rule in rules:
            try:
                if await evaluate_conditions(rule["conditions"], facts, context, rules):
                    results.append({
                        "context": rule["context"],
                        "rule_name": rule["name"], 
                        "priority": rule["priority"],
                        "actions": rule["actions"]
                    })
            except Exception as rule_error:
                logger.error(f"Error evaluating rule {rule.get('name')}: {str(rule_error)}")
                # Continue with other rules
                
        return {"matches": results}
    
    except Exception as e:
        logger.error(f"Evaluation error: {str(e)}", exc_info=True)
        raise HTTPException(status_code=500, detail="Evaluation failed")

@app.post("/validate_rules/")
async def validate_rules(
    file: UploadFile = File(...),
    db: AsyncSession = Depends(get_db),
    sample_facts: Optional[Dict[str, Any]] = None
):
    """
    Validate rules without uploading them to database
    
    Args:
        file: Uploaded file (Excel or JSON)
        db: Database session
        sample_facts: Optional sample facts to test rule evaluation
        
    Returns:
        dict: Validation results
    """
    try:
        # Similar file processing logic as in upload_rules
        filename = file.filename.lower()
        temp_path = f"/tmp/{filename}"
        with open(temp_path, "wb") as buffer:
            buffer.write(await file.read())
        
        uploader = ExcelRuleUploader(db)
        
        if filename.endswith(('.xlsx', '.xls')):
            rules_data = await uploader.validate_excel_structure(temp_path)
        elif filename.endswith('.json'):
            with open(temp_path, 'r') as f:
                rules_data = json.load(f)
                if not isinstance(rules_data, (list, dict)):
                    raise HTTPException(
                        status_code=400,
                        detail="JSON must be an array of rules or a single rule object"
                    )
        else:
            raise HTTPException(
                status_code=400, 
                detail="Unsupported file type. Use .xlsx, .xls, or .json"
            )
        
        # Clean up temporary file
        if os.path.exists(temp_path):
            os.remove(temp_path)
        
        # Convert single rule to list format if needed
        if isinstance(rules_data, dict):
            rules_data = [rules_data]
            
        # Validate rules
        validator = RuleValidator(db)
        is_valid, validation_errors = await validator.validate_rule_set(rules_data)
        
        # Test evaluation if requested
        test_results = []
        if sample_facts and is_valid:
            for rule in rules_data:
                eval_result = await validator.test_evaluate_rule(rule, sample_facts)
                test_results.append({
                    "rule_name": rule.get('name'),
                    "evaluation_result": eval_result
                })
        
        return {
            "valid": is_valid,
            "validation_errors": validation_errors,
            "rule_count": len(rules_data),
            "test_results": test_results if sample_facts and is_valid else None
        }
        
    except Exception as e:
        logger.error(f"Rule validation error: {str(e)}", exc_info=True)
        raise HTTPException(
            status_code=500,
            detail=f"Validation failed: {str(e)}"
        )    

# --------------------------
# Main Entry Point
# --------------------------
if __name__ == "__main__":
    uvicorn.run(
        app,
        host="0.0.0.0",
        port=8000,
        loop="uvloop",
        timeout_keep_alive=30
    )